import BernoulliRegular.FLT37.LehmerVandiver.CaseII.RealGenerator

/-!
# [II1-PROD-SIGMA-FORMULA] Product-level Washington descent over σ-stable products

The existing `formula_of_etaZeroSpanSingletons` (in `CaseII/SpecificChain.lean`) derives the
descent equation from raw-quotient generators `a_i/b_i = 𝔞(η_i)/𝔞₀` at two roots `η₁,η₂`. Those raw
generators cannot be real (the raw quotient is not σ-stable). For the real → real induction, we
re-derive the descent at the **product level**: working with the σ-stable factors
`(x + y·η)(x + y·η⁻¹) = x² + xy·(η + η⁻¹) + y²` (real when `x, y` are real),
which corresponds to the σ-stable ideal product `𝔞(η)·𝔞(η⁻¹)` (the descent of which is established
in `RealGenerator.lean`).

This file builds the polynomial-identity foundation, then the Cramer-style combination of three
pair-product identities into the descent equation `ε₁ x'^p + ε₂ y'^p = ε₃ ((ζ-1)^m z')^p` with
`x', y', z'` real.

## References
* Washington GTM 83 §9.4 (the descent step).
* Expert review 2026-05-27-3 (the product / conjugate-paired form is the right target).
-/

@[expose] public section

open NumberField IsCyclotomicExtension NumberField.IsCMField Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

private instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **Pair-product polynomial identity (the K⁺ norm of `x + yη`).** For a `37`-th root of unity
`η ∈ 𝓞 K`, the product of the conjugate pair `(x + y·η)(x + y·η³⁶)` equals
`x² + xy·(η + η³⁶) + y²`. When `x, y ∈ 𝓞 K⁺` (real), this product is real (the coefficient
`η + η³⁶ = η + η⁻¹` is fixed by complex conjugation). This is the foundational identity for the
σ-stable / product-level Washington descent: the σ-stable ideal product `𝔞(η)·𝔞(η⁻¹)` is generated
by such pair products. -/
theorem caseII_pair_product_eq (x y η : 𝓞 K) (hη : η ^ 37 = 1) :
    (x + y * η) * (x + y * η ^ 36) = x ^ 2 + x * y * (η + η ^ 36) + y ^ 2 := by
  linear_combination y ^ 2 * hη

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The K⁺-trace `η + η⁻¹` is real** (fixed by complex conjugation). For `η^37 = 1`,
`σ(η + η³⁶) = η³⁶ + η = η + η³⁶` since complex conjugation inverts roots of unity
(`caseII_ringOfIntegersComplexConj_root_of_unity`). This is what makes the pair-product
`x² + xy·(η + η⁻¹) + y²` real when `x, y ∈ 𝓞 K⁺`. -/
theorem caseII_eta_plus_etaInv_fixed {η : 𝓞 K} (hη : η ^ 37 = 1) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (η + η ^ 36) = η + η ^ 36 := by
  rw [map_add, map_pow, caseII_ringOfIntegersComplexConj_root_of_unity hη]
  have hpow : (η ^ 36) ^ 36 = η := by
    rw [← pow_mul, show 36 * 36 = 37 * 35 + 1 by norm_num, pow_add, pow_mul, hη]
    ring
  rw [hpow]
  ring

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The pair product `(x + yη)(x + yη⁻¹)` is real when `x, y` are real.** Combining
`caseII_pair_product_eq` (the polynomial identity giving the product as
`x² + xy·(η + η³⁶) + y²`) with `caseII_eta_plus_etaInv_fixed` (the K⁺-trace is σ-fixed) and the
reality hypotheses `σ x = x`, `σ y = y`. Every factor of the σ-stable factorization of `x^p + y^p`
into K⁺ pair products is real, which is what makes the product-level descent variables real. -/
theorem caseII_pair_product_fixed {x y η : 𝓞 K}
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y)
    (hη : η ^ 37 = 1) :
    NumberField.IsCMField.ringOfIntegersComplexConj K ((x + y * η) * (x + y * η ^ 36)) =
      (x + y * η) * (x + y * η ^ 36) := by
  rw [caseII_pair_product_eq x y η hη, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
    hx, hy, caseII_eta_plus_etaInv_fixed hη]

/-- **Pair-anchored ideal identity: `(𝔪·𝔠(η)·𝔭)·(𝔪·𝔠(η⁻¹)·𝔭) = span{(x+yη)(x+yη⁻¹)}`.**
The product at η and η⁻¹ of the existing `m_mul_c_mul_p` identities, packaged into the
pair principal ideal. Combined with `caseII_pair_product_eq` (the generator is real for real
`x, y`), this is the bridge from the σ-stable ideal product to the **real** pair generator. -/
theorem caseII_pair_principal_ideal_eq {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) *
      (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) =
      Ideal.span ({(D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * ((caseII_etaInv η : 𝓞 K))) } :
        Set (𝓞 K)) := by
  have h1 := m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have h2 := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
  rw [h1, h2, Ideal.span_singleton_mul_span_singleton]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The pair product `(x + yη)(x + yη⁻¹)` descends to `𝓞 K⁺`.** When `x, y` are real,
the pair product is σ-fixed (`caseII_pair_product_fixed`), hence lies in the image of
`algebraMap (𝓞 K⁺) (𝓞 K)`. This is the polynomial-to-`𝓞 K⁺` bridge that lets the σ-stable
ideal-product generator be packaged as a real element for the descent. -/
theorem caseII_pair_product_descends {x y η : 𝓞 K}
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y)
    (hη : η ^ 37 = 1) :
    (x + y * η) * (x + y * η ^ 36) ∈
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mp
    (caseII_pair_product_fixed hx hy hη)

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The real `𝓞 K⁺`-preimage of the pair product.** For real `x, y` and `η^37 = 1`, the
preimage element `p⁺ ∈ 𝓞 K⁺` satisfying `algebraMap p⁺ = (x + yη)·(x + yη⁻¹)`. Concretely the
classical choice from `caseII_pair_product_descends`. -/
noncomputable def caseII_pair_realGenerator {x y η : 𝓞 K}
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y)
    (hη : η ^ 37 = 1) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_pair_product_descends hx hy hη).choose

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Defining identity of `caseII_pair_realGenerator`.** -/
@[simp] theorem caseII_pair_realGenerator_spec {x y η : 𝓞 K}
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y)
    (hη : η ^ 37 = 1) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_pair_realGenerator hx hy hη) =
      (x + y * η) * (x + y * η ^ 36) :=
  (caseII_pair_product_descends hx hy hη).choose_spec

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The K⁺-trace `η + η⁻¹` descends to `𝓞 K⁺`.** Immediate from `caseII_eta_plus_etaInv_fixed`
+ `ringOfIntegersComplexConj_eq_self_iff`. Reusable for pair-Vandermonde coefficients
`γ_i - γ_j ∈ 𝓞 K⁺` in the product-level Cramer combination. -/
theorem caseII_eta_trace_descends {η : 𝓞 K} (hη : η ^ 37 = 1) :
    η + η ^ 36 ∈
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mp
    (caseII_eta_plus_etaInv_fixed hη)

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Concrete `𝓞 K⁺` preimage of `η + η⁻¹`.** Classical choice from `caseII_eta_trace_descends`. -/
noncomputable def caseII_eta_trace {η : 𝓞 K} (hη : η ^ 37 = 1) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_eta_trace_descends hη).choose

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Defining identity of `caseII_eta_trace`.** -/
@[simp] theorem caseII_eta_trace_spec {η : 𝓞 K} (hη : η ^ 37 = 1) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_eta_trace hη) = η + η ^ 36 :=
  (caseII_eta_trace_descends hη).choose_spec

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The K⁺-level real-polynomial identity for the pair generator.** When `x, y` are images of
real elements `xP, yP ∈ 𝓞 K⁺`, the pair generator `(x + yη)(x + yη⁻¹)` is the K⁺-algebraMap image
of `x⁺² + x⁺·y⁺·(η + η⁻¹)⁺ + y⁺²`. This is the genuine product-level descent variable form. -/
theorem caseII_pair_realGenerator_eq_real_polynomial
    (xP yP : 𝓞 (NumberField.maximalRealSubfield K)) {η : 𝓞 K} (hη : η ^ 37 = 1) :
    haveI hxP : NumberField.IsCMField.ringOfIntegersComplexConj K
        (algebraMap _ _ xP) = algebraMap _ _ xP :=
      (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mpr ⟨xP, rfl⟩
    haveI hyP : NumberField.IsCMField.ringOfIntegersComplexConj K
        (algebraMap _ _ yP) = algebraMap _ _ yP :=
      (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mpr ⟨yP, rfl⟩
    caseII_pair_realGenerator (η := η) hxP hyP hη =
      xP ^ 2 + xP * yP * caseII_eta_trace hη + yP ^ 2 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [caseII_pair_realGenerator_spec, caseII_pair_product_eq _ _ _ hη, map_add, map_add,
    map_mul, map_mul, map_pow, map_pow, caseII_eta_trace_spec]

/-- **`D.x` descends to `𝓞 K⁺`.** Immediate from `D.x_real` (the reality field of
`RealCaseIIData37`) + `ringOfIntegersComplexConj_eq_self_iff`. -/
theorem caseII_realCaseIIData_x_descends {m : ℕ} (D : RealCaseIIData37 K m) :
    D.x ∈ Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mp D.x_real

/-- **`D.y` descends to `𝓞 K⁺`.** -/
theorem caseII_realCaseIIData_y_descends {m : ℕ} (D : RealCaseIIData37 K m) :
    D.y ∈ Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mp D.y_real

/-- **`σ`-fixed-data pair generator descends to `𝓞 K⁺`.** For a `RealCaseIIData37` and any
`η ∈ nthRootsFinset 37 1`, the pair product `(D.x + D.y·η)(D.x + D.y·η³⁶)` is in the image of
`algebraMap (𝓞 K⁺) (𝓞 K)`. -/
theorem caseII_data_pair_product_descends {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * ((η : 𝓞 K) ^ 36)) ∈
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  caseII_pair_product_descends D.x_real D.y_real
    ((mem_nthRootsFinset (by norm_num) _).mp η.2)

/-- **`σ`-fixed-data concrete pair real generator.** The `𝓞 K⁺` element generating the σ-stable
pair principal ideal for `RealCaseIIData37`. -/
noncomputable def caseII_data_pair_realGenerator {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  caseII_pair_realGenerator D.x_real D.y_real
    ((mem_nthRootsFinset (by norm_num) _).mp η.2)

/-- **Defining identity of `caseII_data_pair_realGenerator`.** -/
@[simp] theorem caseII_data_pair_realGenerator_spec {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_data_pair_realGenerator D η) =
      (D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * ((η : 𝓞 K) ^ 36)) :=
  caseII_pair_realGenerator_spec D.x_real D.y_real
    ((mem_nthRootsFinset (by norm_num) _).mp η.2)

/-- **The concrete `𝓞 K⁺` real preimage of `D.x`** (`xP` in the descent variable notation). -/
noncomputable def caseII_data_xP {m : ℕ} (D : RealCaseIIData37 K m) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_realCaseIIData_x_descends D).choose

/-- **Defining identity of `caseII_data_xP`.** -/
@[simp] theorem caseII_data_xP_spec {m : ℕ} (D : RealCaseIIData37 K m) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_data_xP D) = D.x :=
  (caseII_realCaseIIData_x_descends D).choose_spec

/-- **The concrete `𝓞 K⁺` real preimage of `D.y`** (`yP`). -/
noncomputable def caseII_data_yP {m : ℕ} (D : RealCaseIIData37 K m) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_realCaseIIData_y_descends D).choose

/-- **Defining identity of `caseII_data_yP`.** -/
@[simp] theorem caseII_data_yP_spec {m : ℕ} (D : RealCaseIIData37 K m) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_data_yP D) = D.y :=
  (caseII_realCaseIIData_y_descends D).choose_spec

/-- **The data-level K⁺-polynomial identity for the pair generator.** Combines
`caseII_data_pair_realGenerator_spec` (the pair product is the algebraMap image of the data pair
generator), `caseII_pair_product_eq` (the polynomial pair product identity), and the K⁺ data parts
`D.xP, D.yP`. The pair generator equals `D.xP² + D.xP·D.yP·γ_η + D.yP²` in `𝓞 K⁺`, with
`γ_η = caseII_eta_trace`. This is the genuine product-level descent variable expression. -/
theorem caseII_data_pair_realGenerator_eq_polynomial {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator D η =
      caseII_data_xP D ^ 2 +
        caseII_data_xP D * caseII_data_yP D *
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η.2) +
        caseII_data_yP D ^ 2 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  have hη : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  rw [caseII_data_pair_realGenerator_spec, caseII_pair_product_eq _ _ _ hη, map_add, map_add,
    map_mul, map_mul, map_pow, map_pow, caseII_data_xP_spec, caseII_data_yP_spec,
    caseII_eta_trace_spec]

/-- **Difference of pair generators isolates the cross term.** For `D : RealCaseIIData37` and two
roots `η₁, η₂`, the pair generators at `η₁` and `η₂` (in `𝓞 K⁺`) differ by `xP·yP·(γ_{η₁} - γ_{η₂})`
where `γ` is the K⁺-trace. Immediate from `caseII_data_pair_realGenerator_eq_polynomial` + `ring`.
This is the **Cramer-step building block**: pair-product differences give the cross term `xP·yP`
when divided by the K⁺-trace difference, exposing the descent variable's bilinear structure. -/
theorem caseII_pair_diff_eq_cross_term {m : ℕ} (D : RealCaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator D η₁ - caseII_data_pair_realGenerator D η₂ =
      caseII_data_xP D * caseII_data_yP D *
        (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2)) := by
  rw [caseII_data_pair_realGenerator_eq_polynomial,
    caseII_data_pair_realGenerator_eq_polynomial]
  ring

/-- **Vandermonde-2 extraction of `xP² + yP²` from two pair products.** From two pair products at
distinct K⁺-traces, the sum of squares `xP² + yP²` is the K⁺-linear combination
`(P(η₂)·γ_{η₁} - P(η₁)·γ_{η₂}) / (γ_{η₁} - γ_{η₂})`. Combined with `caseII_pair_diff_eq_cross_term`
(`xP·yP` from difference), this is the SECOND Cramer-step building block — together they fully
determine the bilinear form `(xP, yP)` from two pair products. -/
theorem caseII_pair_combine_eq_sum_squares {m : ℕ} (D : RealCaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_data_xP D ^ 2 + caseII_data_yP D ^ 2) *
        (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2)) =
      caseII_data_pair_realGenerator D η₂ *
        caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) -
      caseII_data_pair_realGenerator D η₁ *
        caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) := by
  rw [caseII_data_pair_realGenerator_eq_polynomial,
    caseII_data_pair_realGenerator_eq_polynomial]
  ring

/-- **Cramer-extracted `(xP + yP)²`** from two pair products at distinct K⁺-traces. Combines
`caseII_pair_diff_eq_cross_term` (giving `xP·yP`) and `caseII_pair_combine_eq_sum_squares`
(giving `xP² + yP²`) via `(xP + yP)² = (xP² + yP²) + 2·xP·yP`. Reusable Cramer composite for
expressing K⁺ descent variable candidates from σ-stable pair products. -/
theorem caseII_pair_xPyPsum_sq_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_data_xP D + caseII_data_yP D) ^ 2 *
        (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2)) =
      caseII_data_pair_realGenerator D η₁ *
          (2 - caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2)) +
        caseII_data_pair_realGenerator D η₂ *
          (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) - 2) := by
  rw [caseII_data_pair_realGenerator_eq_polynomial,
    caseII_data_pair_realGenerator_eq_polynomial]
  ring

/-- **Cramer-extracted `(xP - yP)²`** (symmetric to `caseII_pair_xPyPsum_sq_eq`). -/
theorem caseII_pair_xPyPsub_sq_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_data_xP D - caseII_data_yP D) ^ 2 *
        (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2)) =
      caseII_data_pair_realGenerator D η₂ *
          (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) + 2) -
        caseII_data_pair_realGenerator D η₁ *
          (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) + 2) := by
  rw [caseII_data_pair_realGenerator_eq_polynomial,
    caseII_data_pair_realGenerator_eq_polynomial]
  ring

/-- **Pair principal ideal as the σ-stable p-th power times `𝔪²·𝔭²`.** Substituting
`𝔠 η = 𝔞(η) ^ 37` (`root_div_zeta_sub_one_dvd_gcd_spec`) twice into
`caseII_pair_principal_ideal_eq` (`𝔪·𝔠(η)·𝔭·𝔪·𝔠(η⁻¹)·𝔭 = pair_product`) gives
`pair_product = 𝔪² · 𝔭² · (𝔞(η)·𝔞(η⁻¹))^37`. This is the **σ-stable p-th-power
identity in `𝓞 K`**: the pair principal ideal is the `𝔪²·𝔭²`-scaled p-th power
of the σ-stable Washington ideal `𝔞(η)·𝔞(η⁻¹)` that is the extension of the
descended `J` (via `caseII_sigma_stable_ideal_descends`). It is the bridge that
lets the pair generator serve as a concrete witness for the abstract descent
identity. -/
theorem caseII_pair_principal_eq_pth_power {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    Ideal.span ({(D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * ((caseII_etaInv η : 𝓞 K))) } :
        Set (𝓞 K)) =
      (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))) ^ 2 *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ 2 *
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 := by
  have hpair := caseII_pair_principal_ideal_eq D hp η
  have hspec := root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η
  have hspecinv :=
    root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)
  rw [← hpair, mul_pow, hspec, hspecinv]
  ring

/-- **Two-prime pair-product / σ-stable-ideal p-th power cross identity.** Combining
`caseII_pair_principal_eq_pth_power` at `η` and at `η₀`, the cross-multiplied
identity
`(pair_product at η₀)·(𝔞(η)·𝔞(η⁻¹))^37 = (pair_product at η)·(𝔞(η₀)·𝔞(η₀⁻¹))^37`
holds in `𝓞 K`, because both sides equal `𝔪²·𝔭²·(𝔞(η₀)·𝔞(η₀⁻¹))^37·(𝔞(η)·𝔞(η⁻¹))^37`.
This is the **σ-stable p-th-power descent identity at the `𝓞 K`-level**: pair products
serve as concrete p-th-power-class-witnessing principal generators relating the
two σ-stable Washington ideals at `η` and `η₀`. After descent to `𝓞 K⁺` (faithful
flatness) and p-th-root extraction (`h_VC`: 37 coprime to `|Cl(𝓞 K⁺)|`), this becomes
the linear descent identity `(x)·J_η = (y)·J_η₀` of
`caseII_descended_anchored_real_generators`. -/
theorem caseII_pair_two_prime_cross_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η η₀ : nthRootsFinset 37 (1 : 𝓞 K)) :
    Ideal.span ({(D.x + D.y * (η₀ : 𝓞 K)) *
        (D.x + D.y * ((caseII_etaInv η₀ : 𝓞 K))) } : Set (𝓞 K)) *
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 =
    Ideal.span ({(D.x + D.y * (η : 𝓞 K)) *
        (D.x + D.y * ((caseII_etaInv η : 𝓞 K))) } : Set (𝓞 K)) *
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₀ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
          (caseII_etaInv η₀)) ^ 37 := by
  rw [caseII_pair_principal_eq_pth_power D hp η₀,
    caseII_pair_principal_eq_pth_power D hp η]
  ring

/-- **Two-prime pair-product cross identity, descended to `𝓞 K⁺`.** The σ-stable
p-th-power descent identity from `caseII_pair_two_prime_cross_eq` (in `𝓞 K`)
descends to `𝓞 K⁺`: for the descended ideals `J, J₀ : Ideal (𝓞 K⁺)` (from
`caseII_sigma_stable_ideal_descends` at `η` and `η₀`), the cross identity
`(pair_gen_K⁺ D η₀) · J^37 = (pair_gen_K⁺ D η) · J₀^37` holds. Proof: apply
`Ideal.map (algebraMap (𝓞 K⁺) (𝓞 K))` to both sides — using `Ideal.map_mul`,
`Ideal.map_pow`, `caseII_data_pair_realGenerator_spec`, and the descent
hypotheses `hJ`, `hJ₀` — the result is the `𝓞 K` identity, which holds by
`caseII_pair_two_prime_cross_eq`; then `map_comap_eq_ringOfIntegers` gives
injectivity of `Ideal.map` under faithful flatness, descending the equality. -/
theorem caseII_pair_two_prime_cross_descends {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η η₀ : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₀ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₀)) :
    Ideal.span ({caseII_data_pair_realGenerator D η₀} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) * J ^ 37 =
      Ideal.span ({caseII_data_pair_realGenerator D η} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) * J₀ ^ 37 := by
  set f : 𝓞 (NumberField.maximalRealSubfield K) →+* 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) with hf
  have hmap :
      (Ideal.span ({caseII_data_pair_realGenerator D η₀} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) * J ^ 37).map f =
        (Ideal.span ({caseII_data_pair_realGenerator D η} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) * J₀ ^ 37).map f := by
    rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_pow, Ideal.map_pow,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      hJ, hJ₀, caseII_data_pair_realGenerator_spec, caseII_data_pair_realGenerator_spec]
    exact caseII_pair_two_prime_cross_eq D hp η η₀
  have hcomap := congrArg (Ideal.comap f) hmap
  rwa [BernoulliRegular.map_comap_eq_ringOfIntegers K,
    BernoulliRegular.map_comap_eq_ringOfIntegers K] at hcomap

/-- **Three-prime Vandermonde linear dependence of pair generators.** For
`D : RealCaseIIData37` and three roots `η₁, η₂, η₃ ∈ nthRootsFinset 37 1`,
the pair generators satisfy the Vandermonde identity
`(γ_η₁ - γ_η₂) · P(η₃) + (γ_η₂ - γ_η₃) · P(η₁) + (γ_η₃ - γ_η₁) · P(η₂) = 0`
in `𝓞 K⁺`, where `γ_η = caseII_eta_trace` and `P(η) = caseII_data_pair_realGenerator D η`.
Proof: substitute the K⁺-polynomial form `P(η) = xP² + xP·yP·γ_η + yP²`
(`caseII_data_pair_realGenerator_eq_polynomial`); the constant (`xP² + yP²`) terms
cancel because the three coefficients sum to zero, and the linear-in-γ terms
cancel by the symmetric Vandermonde identity. This is the natural consistency
check enforcing that *any three* pair generators at distinct K⁺-traces lie on a
common affine line — the geometric statement that the Cramer extractions
(`xP·yP`, `xP² + yP²`, `(xP±yP)²`) are well-defined independent of the
choice of two-prime extraction pair, the σ-stable analog of the raw-quotient
3-anchor consistency in `formula_of_etaZeroSpanSingletons`. -/
theorem caseII_pair_three_prime_vandermonde {m : ℕ} (D : RealCaseIIData37 K m)
    (η₁ η₂ η₃ : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) -
        caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2)) *
        caseII_data_pair_realGenerator D η₃ +
      (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₃.2)) *
        caseII_data_pair_realGenerator D η₁ +
      (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₃.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2)) *
        caseII_data_pair_realGenerator D η₂ = 0 := by
  rw [caseII_data_pair_realGenerator_eq_polynomial,
    caseII_data_pair_realGenerator_eq_polynomial,
    caseII_data_pair_realGenerator_eq_polynomial]
  ring

/-- **σ-stable pth-power relation between K⁺-pair generators (the descent algebra core).** Given
the σ-stable anchored real generator pair `(x, y) ∈ (𝓞 K⁺)²` with `(x)·J = (y)·J₀` from
`caseII_descended_anchored_real_generators`, the K⁺-pair generators `P(η_0), P(η)` satisfy
`P(η_0)·y^37 ≈ x^37·P(η)` as K⁺-ideals (associated, by a K⁺-unit). This combines:
* `caseII_pair_two_prime_cross_descends`: `span{P(η_0)}·J^37 = span{P(η)}·J_0^37` in `𝓞 K⁺`.
* 37th power of `(x)·J = (y)·J_0`: `span{x^37}·J^37 = span{y^37}·J_0^37` in `𝓞 K⁺`.

Multiplying the first by `span{y^37}` and the second by `span{P(η)}`, both sides have equal RHS
`span{y^37·P(η)}·J_0^37`, so the LHS's are equal:
`span{P(η_0)·y^37}·J^37 = span{x^37·P(η)}·J^37`.

Cancelling `J^37` (non-zero in the Dedekind ring of integers `𝓞 K⁺`) gives the principal-ideal
equality `span{P(η_0)·y^37} = span{x^37·P(η)}`, equivalently `Associated`. This is the
**product-level σ-stable analog of Washington's pth-power equation
`a_i·b_j^p = unit·(stuff)·a_j·b_i^p`**, the engine of the Cramer descent step: the K⁺-pair
generators play the role of `a_i^p` and `b_i^p`. -/
theorem caseII_pair_pth_power_relation {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ_ne : J ≠ ⊥)
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x y : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy : Ideal.span ({x} : Set _) * J = Ideal.span ({y} : Set _) * J₀) :
    Associated
      (caseII_data_pair_realGenerator D D.etaZero * y ^ 37)
      (x ^ 37 * caseII_data_pair_realGenerator D η) := by
  rw [← Ideal.span_singleton_eq_span_singleton]
  have hcross := caseII_pair_two_prime_cross_descends D hp η D.etaZero hJ hJ0
  have hxy37 :
      Ideal.span ({x ^ 37} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) * J ^ 37 =
        Ideal.span ({y ^ 37} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) * J₀ ^ 37 := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← mul_pow, ← mul_pow, hxy]
  have hJ_pow : J ^ 37 ≠ ⊥ := pow_ne_zero 37 hJ_ne
  refine mul_right_cancel₀ hJ_pow ?_
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  calc
    Ideal.span ({caseII_data_pair_realGenerator D D.etaZero} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) *
        Ideal.span ({y ^ 37} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) * J ^ 37
      = Ideal.span ({y ^ 37} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) *
          (Ideal.span ({caseII_data_pair_realGenerator D D.etaZero} :
              Set (𝓞 (NumberField.maximalRealSubfield K))) * J ^ 37) := by
        rw [mul_comm (Ideal.span ({caseII_data_pair_realGenerator D D.etaZero} :
          Set (𝓞 (NumberField.maximalRealSubfield K)))), mul_assoc]
    _ = Ideal.span ({y ^ 37} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) *
          (Ideal.span ({caseII_data_pair_realGenerator D η} :
              Set (𝓞 (NumberField.maximalRealSubfield K))) * J₀ ^ 37) := by
        rw [hcross]
    _ = Ideal.span ({caseII_data_pair_realGenerator D η} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) *
          (Ideal.span ({y ^ 37} :
              Set (𝓞 (NumberField.maximalRealSubfield K))) * J₀ ^ 37) := by
        rw [← mul_assoc,
          mul_comm (Ideal.span ({y ^ 37} :
            Set (𝓞 (NumberField.maximalRealSubfield K))))
            (Ideal.span ({caseII_data_pair_realGenerator D η} :
              Set (𝓞 (NumberField.maximalRealSubfield K)))), mul_assoc]
    _ = Ideal.span ({caseII_data_pair_realGenerator D η} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) *
          (Ideal.span ({x ^ 37} :
              Set (𝓞 (NumberField.maximalRealSubfield K))) * J ^ 37) := by
        rw [← hxy37]
    _ = Ideal.span ({x ^ 37} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) *
          Ideal.span ({caseII_data_pair_realGenerator D η} :
            Set (𝓞 (NumberField.maximalRealSubfield K))) * J ^ 37 := by
        rw [← mul_assoc,
          mul_comm (Ideal.span ({caseII_data_pair_realGenerator D η} :
            Set (𝓞 (NumberField.maximalRealSubfield K))))
            (Ideal.span ({x ^ 37} :
              Set (𝓞 (NumberField.maximalRealSubfield K))))]

/-- **The K⁺-unit witnessing the pth-power Associated relation.** From
`caseII_pair_pth_power_relation` (`Associated (P(η₀)·y^37) (x^37·P(η))`), pick the unit
`ε ∈ (𝓞 K⁺)ˣ` with `ε · (P(η₀)·y^37) = x^37·P(η)`. Concretely the classical choice of the
`Associated` constructor's witness. -/
noncomputable def caseII_pair_pth_power_unit {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ_ne : J ≠ ⊥)
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x y : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy : Ideal.span ({x} : Set _) * J = Ideal.span ({y} : Set _) * J₀) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  (caseII_pair_pth_power_relation D hp η hJ_ne hJ hJ0 hxy).choose

/-- **Defining identity of `caseII_pair_pth_power_unit`.** The chosen unit `ε` satisfies
`ε · (P(η₀)·y^37) = x^37·P(η)`. -/
@[simp] theorem caseII_pair_pth_power_unit_spec {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ_ne : J ≠ ⊥)
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x y : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy : Ideal.span ({x} : Set _) * J = Ideal.span ({y} : Set _) * J₀) :
    caseII_data_pair_realGenerator D D.etaZero * y ^ 37 *
        (caseII_pair_pth_power_unit D hp η hJ_ne hJ hJ0 hxy : _) =
      x ^ 37 * caseII_data_pair_realGenerator D η :=
  (caseII_pair_pth_power_relation D hp η hJ_ne hJ hJ0 hxy).choose_spec

/-- **The K⁺ Fermat-like pair-product equation between two primes.** Given two descent
witnesses for `caseII_descended_anchored_real_generators` at distinct roots `η₁, η₂`
(both anchored to `η₀`), the `Associated`-unit-extracted pth-power-relations
(`caseII_pair_pth_power_unit_spec`) combine into the K⁺ identity
`ε₂ · (x₁·y₂)^37 · P(η₁) = ε₁ · (x₂·y₁)^37 · P(η₂)`,
where `P(η) = caseII_data_pair_realGenerator D η` and `ε_i` is the K⁺-unit chosen by
`caseII_pair_pth_power_unit` for the descent at `η_i`. This is the **σ-stable pair-product
Cramer descent equation in `𝓞 K⁺`**: the product-level analog of Washington's
`a_i·b_j^p = unit·(stuff)·a_j·b_i^p` six-unit equation, fully descended to the real
subfield. Combined with `caseII_pair_three_prime_vandermonde` and the Cramer building
blocks, this is the K⁺-level Fermat-equation engine driving the next descent step. -/
theorem caseII_pair_cramer_descent_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ : _) *
        ((x₁ * y₂) ^ 37 * caseII_data_pair_realGenerator D η₁) =
      (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ : _) *
        ((x₂ * y₁) ^ 37 * caseII_data_pair_realGenerator D η₂) := by
  have h1 := caseII_pair_pth_power_unit_spec D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁
  have h2 := caseII_pair_pth_power_unit_spec D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂
  have hlhs1 :
      (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ : _) *
        (y₂ ^ 37 *
          (caseII_data_pair_realGenerator D D.etaZero * y₁ ^ 37 *
            (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ : _))) =
      (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ : _) *
        (y₂ ^ 37 * (x₁ ^ 37 * caseII_data_pair_realGenerator D η₁)) := by
    rw [h1]
  have hlhs2 :
      (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ : _) *
        (y₁ ^ 37 *
          (caseII_data_pair_realGenerator D D.etaZero * y₂ ^ 37 *
            (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ : _))) =
      (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ : _) *
        (y₁ ^ 37 * (x₂ ^ 37 * caseII_data_pair_realGenerator D η₂)) := by
    rw [h2]
  have hequiv : (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ : _) *
      (y₂ ^ 37 *
        (caseII_data_pair_realGenerator D D.etaZero * y₁ ^ 37 *
          (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ : _))) =
    (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ : _) *
      (y₁ ^ 37 *
        (caseII_data_pair_realGenerator D D.etaZero * y₂ ^ 37 *
          (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ : _))) := by
    ring
  have h := hlhs1.symm.trans (hequiv.trans hlhs2)
  rw [mul_pow, mul_pow]
  linear_combination h

/-- **Exists-solution packaging of the σ-stable Cramer descent equation.** Given two
descent witnesses for `caseII_descended_anchored_real_generators` (both anchored at
`D.etaZero`), the K⁺ Fermat-like Cramer descent equation `caseII_pair_cramer_descent_eq`
produces concrete witnesses `x', y' ∈ 𝓞 K⁺` and units `ε₁, ε₂ ∈ (𝓞 K⁺)ˣ` realising the
pair-product descent identity `ε₂·x'^37·P(η₁) = ε₁·y'^37·P(η₂)` in 𝓞 K⁺. This is the
σ-stable analog of `exists_solution_of_etaZeroSpanSingletons` from the raw-quotient
descent — packaged at the K⁺ / pair-product level. Witnesses: `x' := x₁·y₂`,
`y' := x₂·y₁`, `ε_i := caseII_pair_pth_power_unit ... at η_i`. -/
theorem caseII_pair_exists_cramer_solution {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    ∃ (x' y' : 𝓞 (NumberField.maximalRealSubfield K))
      (ε₁ ε₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      x' = x₁ * y₂ ∧ y' = x₂ * y₁ ∧
      (ε₂ : 𝓞 (NumberField.maximalRealSubfield K)) *
          (x' ^ 37 * caseII_data_pair_realGenerator D η₁) =
        (ε₁ : 𝓞 (NumberField.maximalRealSubfield K)) *
          (y' ^ 37 * caseII_data_pair_realGenerator D η₂) :=
  ⟨x₁ * y₂, x₂ * y₁,
    caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁,
    caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂,
    rfl, rfl,
    caseII_pair_cramer_descent_eq D hp η₁ η₂ hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂⟩

/-- **Anchored 4-term pair-product sum identity.** Adding the two pth-power-relations
(`caseII_pair_pth_power_unit_spec`) at distinct test primes `η₁, η₂` (both anchored to
`D.etaZero`) yields the sum decomposition
`(ε₁·y₁^37 + ε₂·y₂^37) · P(η₀) = x₁^37·P(η₁) + x₂^37·P(η₂)` in `𝓞 K⁺`.
This is the **Fermat-like sum identity at the pair-product level**: the LHS is a
linear combination of pair anchor terms, and the RHS is a sum of pair test terms,
all in `𝓞 K⁺`. It is the natural σ-stable analog of the four-term Fermat composite
in the case-II descent chain: pair generators play the role of the per-prime
factor (a/b)^p in the raw-quotient world. -/
theorem caseII_pair_pth_power_sum_form {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    ((caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ :
        𝓞 (NumberField.maximalRealSubfield K)) * y₁ ^ 37 +
      (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ :
        𝓞 (NumberField.maximalRealSubfield K)) * y₂ ^ 37) *
      caseII_data_pair_realGenerator D D.etaZero =
    x₁ ^ 37 * caseII_data_pair_realGenerator D η₁ +
      x₂ ^ 37 * caseII_data_pair_realGenerator D η₂ := by
  have h1 := caseII_pair_pth_power_unit_spec D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁
  have h2 := caseII_pair_pth_power_unit_spec D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂
  linear_combination h1 + h2

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The algebraMap of a `caseII_descended_anchored_real_generators` witness is σ-fixed.**
Trivial wrapper: any `𝓞 K⁺`-element's image under the algebra map to `𝓞 K` is fixed by
the complex conjugation `ringOfIntegersComplexConj K`, because complex conjugation in `K`
restricts to the identity on the totally real subfield `K⁺`. This is the structural
**reality-propagation lemma** for the σ-stable descent: the K⁺-witnesses from
`caseII_descended_anchored_real_generators` automatically supply REAL elements in `𝓞 K`,
ready to be plugged into the Washington-expression-style conjugate-fixed-integral-generator
consumers (e.g.
`CaseIIData37.descent_step_of_adjacent_fixed_integral_generators_and_adaptedKummer`).
-/
theorem caseII_algebraMap_of_descended_real_is_fixed
    (x : 𝓞 (NumberField.maximalRealSubfield K)) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x :=
  (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mpr ⟨x, rfl⟩

/-- **The σ-stable K⁺-Fermat three-prime identity** — combining the three-prime Vandermonde
linear consistency `caseII_pair_three_prime_vandermonde` with the two pth-power-relations
`caseII_pair_pth_power_unit_spec` at `η₁, η₂` (both anchored at `D.etaZero`), we derive the
**K⁺ three-prime Fermat-like identity**

  `P(η₀) · [ε₁·(x₂·y₁)³⁷·(γ_η₂ - γ_η₀) + ε₂·(x₁·y₂)³⁷·(γ_η₀ - γ_η₁)]
    = P(η₀) · [(x₁·x₂)³⁷·(γ_η₂ - γ_η₁)]`

in `𝓞 K⁺`, where `P(η) := caseII_data_pair_realGenerator D η`, `γ_η := caseII_eta_trace η`,
and `εᵢ := caseII_pair_pth_power_unit D … hxyᵢ`. The K⁺-trace differences `γ_η_i - γ_η_j ∈ 𝓞 K⁺`
are σ-fixed (real) and carry the `(ζ - 1)²` content as `𝔭⁺` in `𝓞 K⁺`. This is the **σ-stable
analog of Washington 9.4's three-term `(η_2 - η_0)·…` ε₁·X^p + (η_0 - η_1)·…·ε₂·Y^p =
(η_2 - η_1)·Z^p Cramer identity**, with each cyclotomic difference `η_i - η_j` replaced by the
K⁺-trace difference `γ_η_i - γ_η_j`. The descent variables `X := x₂·y₁`, `Y := x₁·y₂`,
`Z := x₁·x₂ ∈ 𝓞 K⁺` are explicit and REAL. Combined with `P(η₀) ≠ 0` (yet to be shown), this
gives the K⁺ Fermat-like equation between three real descent variables, the σ-stable analog of
`formula_of_etaZeroSpanSingletons`. Proof: `linear_combination` of the Vandermonde and the two
pth-power-relations with coefficients `(x₁·x₂)³⁷, x₂³⁷·(γ_η₂ - γ_η₀), x₁³⁷·(γ_η₀ - γ_η₁)`. -/
theorem caseII_pair_pth_power_three_prime_combo {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    caseII_data_pair_realGenerator D D.etaZero *
        ((caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ :
            𝓞 (NumberField.maximalRealSubfield K)) * (x₂ * y₁) ^ 37 *
            (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
              caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2)) +
          (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ :
              𝓞 (NumberField.maximalRealSubfield K)) * (x₁ * y₂) ^ 37 *
            (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2) -
              caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2))) =
      caseII_data_pair_realGenerator D D.etaZero *
        ((x₁ * x₂) ^ 37 *
          (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
            caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2))) := by
  have hvand := caseII_pair_three_prime_vandermonde D η₁ η₂ D.etaZero
  have h1 := caseII_pair_pth_power_unit_spec D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁
  have h2 := caseII_pair_pth_power_unit_spec D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂
  linear_combination (x₁ ^ 37 * x₂ ^ 37) * hvand +
    (x₂ ^ 37 * (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
        caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2))) * h1 +
    (x₁ ^ 37 * (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2) -
        caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2))) * h2

/-- **The K⁺ pair generator is nonzero.** For any `RealCaseIIData37 D` and root `η`, the
real pair generator `caseII_data_pair_realGenerator D η ∈ 𝓞 K⁺` is nonzero. Reason:
algebraMap into `𝓞 K` is injective (`FaithfulSMul.algebraMap_injective`), and its image
is `(D.x + D.y·η)·(D.x + D.y·η⁻¹)` — a product of two `x_plus_y_mul_ne_zero`-nonzero
factors. This is the **`P(η) ≠ 0` ingredient** required to cancel `P(η₀)` in
`caseII_pair_pth_power_three_prime_combo` and extract the σ-stable K⁺ Fermat sum
equation `ε_1·u_1·X^37 + ε_2·u_2·Y^37 = u_3·Z^37`. -/
theorem caseII_data_pair_realGenerator_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator D η ≠ 0 := by
  intro hzero
  have hmap : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
      (caseII_data_pair_realGenerator D η) = 0 := by
    rw [hzero]
    exact map_zero _
  rw [caseII_data_pair_realGenerator_spec] at hmap
  rcases mul_eq_zero.mp hmap with h | h
  · exact x_plus_y_mul_ne_zero hp D.hζ D.equation D.hz η h
  · exact x_plus_y_mul_ne_zero hp D.hζ D.equation D.hz (caseII_etaInv η) h

/-- **K⁺ three-prime Fermat-like equation (post-`P(η₀)`-cancellation).** Dividing both sides
of `caseII_pair_pth_power_three_prime_combo` by the nonzero K⁺ pair anchor `P(η₀)` (via
`caseII_data_pair_realGenerator_ne_zero` + multiplicative cancellation in the integral domain
`𝓞 K⁺`) gives the σ-stable Fermat-like sum identity
`ε₁·X^37·(γ_η₂ - γ_η₀) + ε₂·Y^37·(γ_η₀ - γ_η₁) = Z^37·(γ_η₂ - γ_η₁)`
directly in `𝓞 K⁺`, where `X := x₂·y₁`, `Y := x₁·y₂`, `Z := x₁·x₂`, and the K⁺-trace
differences `γ_η_i - γ_η_j ∈ 𝓞 K⁺` are σ-fixed. This is the **σ-stable analog of Washington
9.4's `(η₂-η₀)·u₁·X^p + (η₀-η₁)·u₂·Y^p = (η₂-η₁)·((ζ-1)^m·Z)^p` three-term Cramer identity**,
descended to the real subfield. -/
theorem caseII_pair_K_plus_fermat_sum {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ :
        𝓞 (NumberField.maximalRealSubfield K)) * (x₂ * y₁) ^ 37 *
        (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2)) +
      (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ :
          𝓞 (NumberField.maximalRealSubfield K)) * (x₁ * y₂) ^ 37 *
        (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2) -
          caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2)) =
    (x₁ * x₂) ^ 37 *
      (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
        caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2)) := by
  have hcombo :=
    caseII_pair_pth_power_three_prime_combo D hp η₁ η₂ hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂
  have hP0_ne := caseII_data_pair_realGenerator_ne_zero D hp D.etaZero
  exact mul_left_cancel₀ hP0_ne hcombo

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **The K⁺-trace difference `γ_η₁ - γ_η₂` factors as a product of `nthRoots` differences.**
For distinct 37th roots of unity `η₁, η₂` with `η₁ ≠ η₂⁻¹` (i.e. `η₂ ≠ caseII_etaInv η₁`),
the K⁺-trace difference algebraMap image satisfies
`γ_η₁ - γ_η₂ = (η₁ - η₂) · (1 - η₁⁻¹·η₂⁻¹)`
in `𝓞 K`. This is the **first-step factorization** for absorbing the
K⁺-trace-difference coefficient `γ_η₁ - γ_η₂` as a product of differences of
roots of unity (each `Associated (ζ - 1)` by
`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`),
on the way to the Fermat sum identity with unit coefficients. -/
theorem caseII_eta_trace_diff_factorization
    {η₁ η₂ : 𝓞 K} (hη₁ : η₁ ^ 37 = 1) (hη₂ : η₂ ^ 37 = 1) :
    ((η₁ + η₁ ^ 36) - (η₂ + η₂ ^ 36)) =
      (η₁ - η₂) * (1 - η₁ ^ 36 * η₂ ^ 36) := by
  linear_combination η₂ ^ 36 * hη₁ - η₁ ^ 36 * hη₂

omit [NumberField.IsCMField K] in
/-- **K⁺-trace difference Associated `(ζ - 1)²` in `𝓞 K`.** Combining
`caseII_eta_trace_diff_factorization`
`(γ_η₁ - γ_η₂) = (η₁ - η₂) · (1 - η₁^36·η₂^36)` with the mathlib lemma
`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime` (applied to each factor as a
difference of `nthRootsFinset 37`-members), each factor is `Associated (ζ - 1)`, so the
product is `Associated (ζ - 1)²`. Caveats: requires `η₁ ≠ η₂` (so first factor is nonzero
diff) and `η₁·η₂ ≠ 1` (so second factor's other member is ≠ 1 — equivalently
`η₂ ≠ caseII_etaInv η₁`).
This is the **K-level prime-content lemma** for the K⁺-trace difference, enabling the
absorption of `(γ_η_i - γ_η_j)` factors into `(ζ-1)`-power unit decoration in the
Cramer descent chain. -/
theorem caseII_eta_trace_diff_associated_zeta_sub_one_sq
    (hζ : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    {η₁ η₂ : 𝓞 K} (hη₁ : η₁ ^ 37 = 1) (hη₂ : η₂ ^ 37 = 1)
    (hne : η₁ ≠ η₂) (hprod : η₁ * η₂ ≠ 1) :
    Associated (((η₁ + η₁ ^ 36) - (η₂ + η₂ ^ 36)))
      (((zeta_spec 37 ℚ K).toInteger - 1) ^ 2) := by
  rw [caseII_eta_trace_diff_factorization hη₁ hη₂]
  have h1 : Associated ((zeta_spec 37 ℚ K).toInteger - 1) (η₁ - η₂) :=
    hζ.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37)
      ((Polynomial.mem_nthRootsFinset (by norm_num) _).mpr hη₁)
      ((Polynomial.mem_nthRootsFinset (by norm_num) _).mpr hη₂) hne
  have hprod36 : η₁ ^ 36 * η₂ ^ 36 ≠ 1 := by
    rw [← mul_pow]
    intro h
    have h37 : (η₁ * η₂) ^ 37 = 1 := by rw [mul_pow, hη₁, hη₂, one_mul]
    have h36_eq : (η₁ * η₂) ^ 36 * (η₁ * η₂) = 1 := by
      rwa [← pow_succ]
    rw [h, one_mul] at h36_eq
    exact hprod h36_eq
  have hmem1 : (1 : 𝓞 K) ∈ Polynomial.nthRootsFinset 37 (1 : 𝓞 K) :=
    (Polynomial.mem_nthRootsFinset (by norm_num) _).mpr (one_pow _)
  have hmem_prod : η₁ ^ 36 * η₂ ^ 36 ∈ Polynomial.nthRootsFinset 37 (1 : 𝓞 K) :=
    (Polynomial.mem_nthRootsFinset (by norm_num) _).mpr (by
      rw [mul_pow, ← pow_mul, ← pow_mul,
        show 36 * 37 = 37 * 36 by norm_num,
        pow_mul, pow_mul, hη₁, hη₂]
      simp)
  have h2 : Associated ((zeta_spec 37 ℚ K).toInteger - 1) (1 - η₁ ^ 36 * η₂ ^ 36) :=
    hζ.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hmem1 hmem_prod hprod36.symm
  rw [sq]
  exact (h1.mul_mul h2).symm

/-- **The K⁺-trace difference unit `u_{ij}`** (defining `(η_i + η_i⁻¹) - (η_j + η_j⁻¹) =
u_{ij}·(ζ-1)²`). The Associated relation
`caseII_eta_trace_diff_associated_zeta_sub_one_sq` extracts a concrete unit witness via the
classical choice. -/
noncomputable def caseII_eta_trace_diff_unit
    (hζ : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    {η₁ η₂ : 𝓞 K} (hη₁ : η₁ ^ 37 = 1) (hη₂ : η₂ ^ 37 = 1)
    (hne : η₁ ≠ η₂) (hprod : η₁ * η₂ ≠ 1) : (𝓞 K)ˣ :=
  (caseII_eta_trace_diff_associated_zeta_sub_one_sq hζ hη₁ hη₂ hne hprod).choose

omit [NumberField.IsCMField K] in
/-- **Defining identity of `caseII_eta_trace_diff_unit`.** The K⁺-trace difference times the
unit equals `(ζ - 1)²` in `𝓞 K`. -/
@[simp] theorem caseII_eta_trace_diff_unit_spec
    (hζ : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    {η₁ η₂ : 𝓞 K} (hη₁ : η₁ ^ 37 = 1) (hη₂ : η₂ ^ 37 = 1)
    (hne : η₁ ≠ η₂) (hprod : η₁ * η₂ ≠ 1) :
    ((η₁ + η₁ ^ 36) - (η₂ + η₂ ^ 36)) *
        (caseII_eta_trace_diff_unit hζ hη₁ hη₂ hne hprod : 𝓞 K) =
      ((zeta_spec 37 ℚ K).toInteger - 1) ^ 2 :=
  (caseII_eta_trace_diff_associated_zeta_sub_one_sq hζ hη₁ hη₂ hne hprod).choose_spec

omit [NumberField.IsCMField K] in
/-- **The K⁺-trace difference inverse-unit form.** Rearranging
`caseII_eta_trace_diff_unit_spec`: the K⁺-trace difference algebraMap image equals
`(ζ - 1)²` times the unit inverse. Useful for substituting the trace coefficient by
`(ζ-1)²·(unit)` in the Fermat-style equations. -/
theorem caseII_eta_trace_diff_eq_zeta_sub_one_sq_mul_unit_inv
    (hζ : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    {η₁ η₂ : 𝓞 K} (hη₁ : η₁ ^ 37 = 1) (hη₂ : η₂ ^ 37 = 1)
    (hne : η₁ ≠ η₂) (hprod : η₁ * η₂ ≠ 1) :
    (η₁ + η₁ ^ 36) - (η₂ + η₂ ^ 36) =
      ((zeta_spec 37 ℚ K).toInteger - 1) ^ 2 *
        (((caseII_eta_trace_diff_unit hζ hη₁ hη₂ hne hprod)⁻¹ :
          (𝓞 K)ˣ) : 𝓞 K) :=
  (caseII_eta_trace_diff_unit hζ hη₁ hη₂ hne hprod).eq_mul_inv_iff_mul_eq.mpr
    (caseII_eta_trace_diff_unit_spec hζ hη₁ hη₂ hne hprod)

/-- **The K⁺ Fermat sum lifted to `𝓞 K`.** Apply `algebraMap (𝓞 K⁺) (𝓞 K)` to the K⁺ identity
`caseII_pair_K_plus_fermat_sum`. The descent variables `x₁·x₂, x₂·y₁, x₁·y₂` and the K⁺-trace
differences become explicit `𝓞 K` elements (σ-fixed, since they come from `𝓞 K⁺` via
`algebraMap`). This is the **`𝓞 K`-level σ-stable Cramer descent equation** with REAL
descent variables, ready for the `(ζ-1)²` factorization of the K⁺-trace coefficients via
`caseII_eta_trace_diff_unit_spec`. -/
theorem caseII_pair_K_fermat_sum_via_algebraMap {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        ((caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ :
            𝓞 (NumberField.maximalRealSubfield K)) * (x₂ * y₁) ^ 37 *
          (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
            caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2)) +
        (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ :
            𝓞 (NumberField.maximalRealSubfield K)) * (x₁ * y₂) ^ 37 *
          (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2) -
            caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2))) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        ((x₁ * x₂) ^ 37 *
          (caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) -
            caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2))) :=
  congrArg _ (caseII_pair_K_plus_fermat_sum D hp η₁ η₂ hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂)

/-- **The K⁺ Fermat sum distributed to `𝓞 K`.** Distributing `algebraMap (𝓞 K⁺) (𝓞 K)` over
the addition, multiplication, power, subtraction, and `caseII_eta_trace_spec` in
`caseII_pair_K_fermat_sum_via_algebraMap` gives the explicit `𝓞 K` form

  `(ε₁ : 𝓞 K) · (alg(x₂·y₁))³⁷ · ((η₂+η₂³⁶) - (D.etaZero+D.etaZero³⁶))
   + (ε₂ : 𝓞 K) · (alg(x₁·y₂))³⁷ · ((D.etaZero+D.etaZero³⁶) - (η₁+η₁³⁶))
   = (alg(x₁·x₂))³⁷ · ((η₂+η₂³⁶) - (η₁+η₁³⁶))`

where `alg` is `algebraMap (𝓞 K⁺) (𝓞 K)`. This is the **σ-stable Cramer descent equation in
`𝓞 K`** with all variables in `𝓞 K` (no `caseII_eta_trace`), ready for the `(ζ-1)²` cancellation
of the K⁺-trace difference coefficients. -/
theorem caseII_pair_K_fermat_sum_distributed {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ :
            𝓞 (NumberField.maximalRealSubfield K))) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁)) ^ 37 *
        (((η₂ : 𝓞 K) + (η₂ : 𝓞 K) ^ 36) -
          ((D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36)) +
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ :
              𝓞 (NumberField.maximalRealSubfield K))) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂)) ^ 37 *
        (((D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36) -
          ((η₁ : 𝓞 K) + (η₁ : 𝓞 K) ^ 36)) =
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂)) ^ 37 *
      (((η₂ : 𝓞 K) + (η₂ : 𝓞 K) ^ 36) - ((η₁ : 𝓞 K) + (η₁ : 𝓞 K) ^ 36)) := by
  simpa only [map_add, map_mul, map_pow, map_sub, caseII_eta_trace_spec] using
    caseII_pair_K_fermat_sum_via_algebraMap D hp η₁ η₂ hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂

/-- **The K⁺ Fermat sum substituted with `(ζ-1)²` factorization.** Substituting each K⁺-trace
difference `(η_i + η_i^36) - (η_j + η_j^36)` by `(ζ-1)² · (unit_ij)⁻¹` via
`caseII_eta_trace_diff_eq_zeta_sub_one_sq_mul_unit_inv` in
`caseII_pair_K_fermat_sum_distributed`. The `𝓞 K` identity becomes a `(ζ-1)²`-factored equation
with explicit `𝓞 K`-unit decorations. This is the **`(ζ-1)²`-pre-cancellation form** of the
σ-stable Cramer descent equation in `𝓞 K`, ready for the cancellation step that gives the
Fermat-style sum identity with unit coefficients. -/
theorem caseII_pair_K_fermat_sum_zeta_sub_one_sq_factored {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hζ' : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    (hne_12 : (η₁ : 𝓞 K) ≠ (η₂ : 𝓞 K))
    (hne_1z : (η₁ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hne_2z : (η₂ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hprod_12 : (η₁ : 𝓞 K) * (η₂ : 𝓞 K) ≠ 1)
    (hprod_1z : (η₁ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    (hprod_2z : (η₂ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    let h_eta2 : (η₂ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₂.2
    let h_etaZ : (D.etaZero : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2
    let h_eta1 : (η₁ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₁.2
    let u_2z := caseII_eta_trace_diff_unit hζ' h_eta2 h_etaZ hne_2z hprod_2z
    let u_z1 := caseII_eta_trace_diff_unit hζ' h_etaZ h_eta1 hne_1z.symm (by
      rw [mul_comm]; exact hprod_1z)
    let u_21 := caseII_eta_trace_diff_unit hζ' h_eta2 h_eta1 hne_12.symm
      (by rw [mul_comm]; exact hprod_12)
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ :
            𝓞 (NumberField.maximalRealSubfield K))) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁)) ^ 37 *
        (((zeta_spec 37 ℚ K).toInteger - 1) ^ 2 * ((u_2z⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) +
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ :
              𝓞 (NumberField.maximalRealSubfield K))) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂)) ^ 37 *
        (((zeta_spec 37 ℚ K).toInteger - 1) ^ 2 * ((u_z1⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂)) ^ 37 *
      (((zeta_spec 37 ℚ K).toInteger - 1) ^ 2 * ((u_21⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) := by
  have h := caseII_pair_K_fermat_sum_distributed D hp η₁ η₂
    hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂
  have h_eta2 : (η₂ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₂.2
  have h_etaZ : (D.etaZero : 𝓞 K) ^ 37 = 1 :=
    (mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2
  have h_eta1 : (η₁ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₁.2
  rw [caseII_eta_trace_diff_eq_zeta_sub_one_sq_mul_unit_inv hζ' h_eta2 h_etaZ
        hne_2z hprod_2z,
      caseII_eta_trace_diff_eq_zeta_sub_one_sq_mul_unit_inv hζ' h_etaZ h_eta1
        hne_1z.symm (by rw [mul_comm]; exact hprod_1z),
      caseII_eta_trace_diff_eq_zeta_sub_one_sq_mul_unit_inv hζ' h_eta2 h_eta1
        hne_12.symm (by rw [mul_comm]; exact hprod_12)] at h
  simp only
  exact h

/-- **The K-level σ-stable Fermat-style equation in `𝓞 K`** (`(ζ-1)²`-cancelled). Factoring
`(ζ-1)²` from each side of `caseII_pair_K_fermat_sum_zeta_sub_one_sq_factored` and cancelling
(using `(ζ-1)² ≠ 0` in the integral domain `𝓞 K`) gives the Fermat-like sum identity

  `(ε₁ : 𝓞 K) · (alg(x₂·y₁))³⁷ · (u_2z)⁻¹ + (ε₂ : 𝓞 K) · (alg(x₁·y₂))³⁷ · (u_z1)⁻¹
   = (alg(x₁·x₂))³⁷ · (u_21)⁻¹`

in `𝓞 K`, where the (ζ-1)² factor has been absorbed/cancelled. The descent variables
`alg(x_2·y_1), alg(x_1·y_2), alg(x_1·x_2) ∈ 𝓞 K` are σ-fixed (real), and the unit coefficients
`(u_ij)⁻¹ ∈ (𝓞 K)ˣ` are explicit. This is the **σ-stable Fermat sum in 𝓞 K**, the target form
for matching `CaseIIData37`-style descent equations. -/
theorem caseII_pair_K_fermat_sum_unit_form {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hζ' : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    (hne_12 : (η₁ : 𝓞 K) ≠ (η₂ : 𝓞 K))
    (hne_1z : (η₁ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hne_2z : (η₂ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hprod_12 : (η₁ : 𝓞 K) * (η₂ : 𝓞 K) ≠ 1)
    (hprod_1z : (η₁ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    (hprod_2z : (η₂ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    let h_eta2 : (η₂ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₂.2
    let h_etaZ : (D.etaZero : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2
    let h_eta1 : (η₁ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₁.2
    let u_2z := caseII_eta_trace_diff_unit hζ' h_eta2 h_etaZ hne_2z hprod_2z
    let u_z1 := caseII_eta_trace_diff_unit hζ' h_etaZ h_eta1 hne_1z.symm (by
      rw [mul_comm]; exact hprod_1z)
    let u_21 := caseII_eta_trace_diff_unit hζ' h_eta2 h_eta1 hne_12.symm
      (by rw [mul_comm]; exact hprod_12)
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ :
            𝓞 (NumberField.maximalRealSubfield K))) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁)) ^ 37 *
        ((u_2z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) +
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ :
              𝓞 (NumberField.maximalRealSubfield K))) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂)) ^ 37 *
        ((u_z1⁻¹ : (𝓞 K)ˣ) : 𝓞 K) =
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂)) ^ 37 *
      ((u_21⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
  intro h_eta2 h_etaZ h_eta1 u_2z u_z1 u_21
  have h := caseII_pair_K_fermat_sum_zeta_sub_one_sq_factored D hp η₁ η₂ hζ'
    hne_12 hne_1z hne_2z hprod_12 hprod_1z hprod_2z hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂
  have hzeta_ne : ((zeta_spec 37 ℚ K).toInteger - 1 : 𝓞 K) ≠ 0 :=
    hζ'.sub_one_ne_zero (by decide : 1 < 37)
  have hzeta_sq_ne : ((zeta_spec 37 ℚ K).toInteger - 1 : 𝓞 K) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hzeta_ne
  refine mul_left_cancel₀ hzeta_sq_ne ?_
  linear_combination h

/-- **The σ-stable Fermat-style equation as `∃ ε_i ∈ (𝓞 K)ˣ, ε_1·X^37 + ε_2·Y^37 = Z^37`.**
Multiplies `caseII_pair_K_fermat_sum_unit_form` through by `u_21` to clear the `(u_21)⁻¹`
factor on the RHS, bundling the resulting `u_21 · (u_2z)⁻¹ · ε_i` factors as `(𝓞 K)ˣ` units.
This is the **clean Fermat-form endpoint** of the σ-stable K⁺ Cramer descent: an `𝓞 K`-level
unit-coefficient three-term identity with σ-fixed REAL descent variables. -/
theorem caseII_pair_K_fermat_sum_exists {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hζ' : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    (hne_12 : (η₁ : 𝓞 K) ≠ (η₂ : 𝓞 K))
    (hne_1z : (η₁ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hne_2z : (η₂ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hprod_12 : (η₁ : 𝓞 K) * (η₂ : 𝓞 K) ≠ 1)
    (hprod_1z : (η₁ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    (hprod_2z : (η₂ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    {J₁ J₂ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ₁_ne : J₁ ≠ ⊥) (hJ₂_ne : J₂ ≠ ⊥)
    (hJ₁ : J₁.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₁))
    (hJ₂ : J₂.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η₂))
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    {x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)}
    (hxy₁ : Ideal.span ({x₁} : Set _) * J₁ = Ideal.span ({y₁} : Set _) * J₀)
    (hxy₂ : Ideal.span ({x₂} : Set _) * J₂ = Ideal.span ({y₂} : Set _) * J₀) :
    ∃ (ε₁' ε₂' : (𝓞 K)ˣ),
      (ε₁' : 𝓞 K) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁)) ^ 37 +
        (ε₂' : 𝓞 K) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂)) ^ 37 =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂)) ^ 37 := by
  have h_eta2 : (η₂ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₂.2
  have h_etaZ : (D.etaZero : 𝓞 K) ^ 37 = 1 :=
    (mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2
  have h_eta1 : (η₁ : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η₁.2
  set u_2z := caseII_eta_trace_diff_unit hζ' h_eta2 h_etaZ hne_2z hprod_2z with hu2z_def
  set u_z1 := caseII_eta_trace_diff_unit hζ' h_etaZ h_eta1 hne_1z.symm (by
    rw [mul_comm]; exact hprod_1z) with huz1_def
  set u_21 := caseII_eta_trace_diff_unit hζ' h_eta2 h_eta1 hne_12.symm
    (by rw [mul_comm]; exact hprod_12) with hu21_def
  set ε₁ := caseII_pair_pth_power_unit D hp η₁ hJ₁_ne hJ₁ hJ₀ hxy₁ with hε1_def
  set ε₂ := caseII_pair_pth_power_unit D hp η₂ hJ₂_ne hJ₂ hJ₀ hxy₂ with hε2_def
  refine ⟨u_21 * u_2z⁻¹ * Units.map (algebraMap _ (𝓞 K)).toMonoidHom ε₁,
          u_21 * u_z1⁻¹ * Units.map (algebraMap _ (𝓞 K)).toMonoidHom ε₂, ?_⟩
  have h := caseII_pair_K_fermat_sum_unit_form D hp η₁ η₂ hζ'
    hne_12 hne_1z hne_2z hprod_12 hprod_1z hprod_2z
    hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂
  simp only at h
  have hu : (u_21 : 𝓞 K) * ((u_21⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := u_21.mul_inv
  have hm : (u_21 : 𝓞 K) *
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (ε₁ : _)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁)) ^ 37 *
          ((u_2z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) +
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (ε₂ : _)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂)) ^ 37 *
          ((u_z1⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
    (u_21 : 𝓞 K) *
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂)) ^ 37 *
        ((u_21⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) := congrArg ((u_21 : 𝓞 K) * ·) h
  have hcoerce₁ :
      (↑(Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom ε₁) :
        𝓞 K) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (ε₁ : _) := rfl
  have hcoerce₂ :
      (↑(Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom ε₂) :
        𝓞 K) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (ε₂ : _) := rfl
  simp only [Units.val_mul, hcoerce₁, hcoerce₂]
  linear_combination hm + (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    (x₁ * x₂)) ^ 37 * hu

/-- **End-to-end σ-stable Fermat sum from `RealCaseIIData37` (anchor `J₀` supplied).**
Composes `caseII_sigma_stable_ideal_descends` (at `η₁`, `η₂`) with
`caseII_descended_anchored_real_generators` (at both test primes against the
caller-supplied anchor `J₀`) and `caseII_pair_K_fermat_sum_exists` to produce the
σ-stable Fermat-style equation `ε₁'·X^37 + ε₂'·Y^37 = Z^37` in `𝓞 K` directly from a
`RealCaseIIData37`, the K⁺ class-number coprimality assumption `h_VC`, choices of
test primes `η₁, η₂`, and a real-ideal-model `J₀` of the anchor pair-product
`𝔞(η₀)·𝔞(η₀⁻¹)`. The anchor `J₀` is taken as a hypothesis because
`caseII_sigma_stable_ideal_descends` requires `η ≠ D.etaZero` and so cannot be
applied at `D.etaZero` itself; the anchor descent is therefore an open input
shared with `caseII_descended_anchored_class_eq`. -/
theorem caseII_pair_K_fermat_sum_of_realCaseIIData37 {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (hζ' : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hη1_ne_z : η₁ ≠ D.etaZero) (hη1inv_ne_z : caseII_etaInv η₁ ≠ D.etaZero)
    (hη2_ne_z : η₂ ≠ D.etaZero) (hη2inv_ne_z : caseII_etaInv η₂ ≠ D.etaZero)
    (hne_12 : (η₁ : 𝓞 K) ≠ (η₂ : 𝓞 K))
    (hne_1z : (η₁ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hne_2z : (η₂ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hprod_12 : (η₁ : 𝓞 K) * (η₂ : 𝓞 K) ≠ 1)
    (hprod_1z : (η₁ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    (hprod_2z : (η₂ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    {J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ₀_ne : J₀ ≠ ⊥)
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    ∃ (x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K))
      (ε₁' ε₂' : (𝓞 K)ˣ),
      (ε₁' : 𝓞 K) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁)) ^ 37 +
        (ε₂' : 𝓞 K) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂)) ^ 37 =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂)) ^ 37 := by
  obtain ⟨J₁, hJ₁⟩ := caseII_sigma_stable_ideal_descends D hp η₁ hη1_ne_z hη1inv_ne_z
  obtain ⟨J₂, hJ₂⟩ := caseII_sigma_stable_ideal_descends D hp η₂ hη2_ne_z hη2inv_ne_z
  have hmul_ne : ∀ η : nthRootsFinset 37 (1 : 𝓞 K),
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ≠ ⊥ := by
    intro η hmul0
    rw [Ideal.mul_eq_bot] at hmul0
    rcases hmul0 with h | h
    · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η h
    · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η) h
  have hJ₁_ne : J₁ ≠ ⊥ := fun h => by
    apply hmul_ne η₁; rw [← hJ₁, h, Ideal.map_bot]
  have hJ₂_ne : J₂ ≠ ⊥ := fun h => by
    apply hmul_ne η₂; rw [← hJ₂, h, Ideal.map_bot]
  obtain ⟨x₁, y₁, _hx₁_ne, _hy₁_ne, hxy₁⟩ :=
    caseII_descended_anchored_real_generators D hp h_VC η₁ hJ₁_ne hJ₀_ne hJ₁ hJ₀
  obtain ⟨x₂, y₂, _hx₂_ne, _hy₂_ne, hxy₂⟩ :=
    caseII_descended_anchored_real_generators D hp h_VC η₂ hJ₂_ne hJ₀_ne hJ₂ hJ₀
  obtain ⟨ε₁', ε₂', heq⟩ :=
    caseII_pair_K_fermat_sum_exists D hp η₁ η₂ hζ'
      hne_12 hne_1z hne_2z hprod_12 hprod_1z hprod_2z
      hJ₁_ne hJ₂_ne hJ₁ hJ₂ hJ₀ hxy₁ hxy₂
  exact ⟨x₁, y₁, x₂, y₂, ε₁', ε₂', heq⟩

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The Fermat-sum descent variables are σ-fixed (real) in `𝓞 K`.** The variables
`X := algebraMap (𝓞 K⁺) (𝓞 K) (x₂·y₁)`, `Y := algebraMap _ _ (x₁·y₂)`,
`Z := algebraMap _ _ (x₁·x₂)` from `caseII_pair_K_fermat_sum_exists` are images of
`𝓞 K⁺`-elements under `algebraMap` and are therefore fixed by the complex
conjugation `ringOfIntegersComplexConj K`. This is the **reality witness for the
σ-stable Fermat-style descent endpoint**: all three terms of the Cramer descent
equation in `𝓞 K` are real, ready to be compared against case-I-shaped FLT37
machinery. -/
theorem caseII_pair_K_fermat_sum_descent_vars_real
    (x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K)) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁)) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₂ * y₁) ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂)) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * y₂) ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂)) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (x₁ * x₂) :=
  ⟨caseII_algebraMap_of_descended_real_is_fixed (K := K) (x₂ * y₁),
    caseII_algebraMap_of_descended_real_is_fixed (K := K) (x₁ * y₂),
    caseII_algebraMap_of_descended_real_is_fixed (K := K) (x₁ * x₂)⟩

/-- **The σ-stable Cramer descent endpoint: a Case-I-form Fermat equation in `𝓞 K` with REAL
descent variables.** Combines `caseII_pair_K_fermat_sum_of_realCaseIIData37` (the Cramer
descent producer) with `caseII_pair_K_fermat_sum_descent_vars_real` (the σ-fixedness witness)
to give the **σ-stable Case-I-form Fermat-style endpoint** of the case-II descent: from a
`RealCaseIIData37` together with VC and test-prime data, the descent variables
`X, Y, Z ∈ 𝓞 K` are explicit, REAL (σ-fixed), and satisfy `ε₁'·X^37 + ε₂'·Y^37 = Z^37`
in `𝓞 K`. This is the **σ-stable Washington 9.4 endpoint** — the σ-stable analog of the
classical Case-II → Case-I descent. The remaining open content is the σ-stable Case-I
impossibility: under `¬37 ∣ hPlus K`, this equation has no solution. -/
theorem caseII_pair_real_caseI_form_of_realCaseIIData37 {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (hζ' : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hη1_ne_z : η₁ ≠ D.etaZero) (hη1inv_ne_z : caseII_etaInv η₁ ≠ D.etaZero)
    (hη2_ne_z : η₂ ≠ D.etaZero) (hη2inv_ne_z : caseII_etaInv η₂ ≠ D.etaZero)
    (hne_12 : (η₁ : 𝓞 K) ≠ (η₂ : 𝓞 K))
    (hne_1z : (η₁ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hne_2z : (η₂ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hprod_12 : (η₁ : 𝓞 K) * (η₂ : 𝓞 K) ≠ 1)
    (hprod_1z : (η₁ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    (hprod_2z : (η₂ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    {J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ₀_ne : J₀ ≠ ⊥)
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    ∃ (X Y Z : 𝓞 K) (ε₁' ε₂' : (𝓞 K)ˣ),
      NumberField.IsCMField.ringOfIntegersComplexConj K X = X ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K Y = Y ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K Z = Z ∧
      (ε₁' : 𝓞 K) * X ^ 37 + (ε₂' : 𝓞 K) * Y ^ 37 = Z ^ 37 := by
  obtain ⟨x₁, y₁, x₂, y₂, ε₁', ε₂', heq⟩ :=
    caseII_pair_K_fermat_sum_of_realCaseIIData37 D hp hζ' h_VC η₁ η₂
      hη1_ne_z hη1inv_ne_z hη2_ne_z hη2inv_ne_z
      hne_12 hne_1z hne_2z hprod_12 hprod_1z hprod_2z hJ₀_ne hJ₀
  obtain ⟨hX_real, hY_real, hZ_real⟩ :=
    caseII_pair_K_fermat_sum_descent_vars_real (K := K) x₁ y₁ x₂ y₂
  exact ⟨_, _, _, ε₁', ε₂', hX_real, hY_real, hZ_real, heq⟩

/-- **Concrete `𝓞 K`-pair-generator from `RealCaseIIData37`** — the algebraMap image of the
K⁺ pair generator. For convenience, packages `caseII_data_pair_realGenerator D η` with its
`𝓞 K`-image (= `(D.x + D.y·η)·(D.x + D.y·η^36)`) and σ-fixedness as a single accessor. -/
noncomputable def caseII_data_pair_realGenerator_K {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) : 𝓞 K :=
  algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    (caseII_data_pair_realGenerator D η)

/-- **The `𝓞 K`-pair-generator equals the polynomial pair product.** -/
@[simp] theorem caseII_data_pair_realGenerator_K_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator_K D η =
      (D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) := by
  unfold caseII_data_pair_realGenerator_K caseII_data_pair_realGenerator
  exact (caseII_data_pair_product_descends D η).choose_spec

/-- **The `𝓞 K`-pair-generator is σ-fixed (REAL).** -/
theorem caseII_data_pair_realGenerator_K_real {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (caseII_data_pair_realGenerator_K D η) =
      caseII_data_pair_realGenerator_K D η :=
  caseII_algebraMap_of_descended_real_is_fixed _

/-- **The σ-stable Cramer descent's principal-ideal-product identity.** Equivalent restatement
of `caseII_pair_principal_ideal_eq` highlighting the K⁺-pair-generator: the principal ideal
generated by `caseII_data_pair_realGenerator_K D η` in `𝓞 K` equals the σ-stable Washington
construction `𝔪² · 𝔭² · 𝔠(η) · 𝔠(η⁻¹)`. This is the **`𝓞 K`-level identity** for the σ-stable
pair-generator, ready for downstream consumers of the σ-stable Washington source. -/
theorem caseII_data_pair_realGenerator_K_principal_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    Ideal.span ({caseII_data_pair_realGenerator_K D η} : Set (𝓞 K)) =
      (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
          divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) *
        (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
          divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
          Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) := by
  rw [caseII_data_pair_realGenerator_K_eq]
  exact (caseII_pair_principal_ideal_eq D hp η).symm

/-- **The K⁺-pair-generator equals the polynomial pair product (K⁺ form).** Combined
restatement of `caseII_pair_realGenerator_spec` for `caseII_data_pair_realGenerator`. -/
@[simp] theorem caseII_data_pair_realGenerator_K_spec_alt {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_data_pair_realGenerator D η) =
      (D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) := by
  have : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  exact caseII_pair_realGenerator_spec D.x_real D.y_real this

/-- **`(ζ-1)² | caseII_data_pair_realGenerator_K D η`**. The σ-stable pair generator
`P_K = (D.x + D.y·η)·(D.x + D.y·η^36)` in `𝓞 K` is divisible by `(ζ-1)²`. From the principal
ideal identity `caseII_pair_principal_ideal_eq`, `span{P_K} = 𝔪·𝔠(η)·𝔭 · 𝔪·𝔠(η⁻¹)·𝔭`. Each
factor is contained in `𝔭` (right absorption), so their product is contained in `𝔭² = span{(ζ-1)²}`,
which gives the divisibility. -/
theorem caseII_zetaSubOne_sq_dvd_data_pair_realGenerator_K {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ caseII_data_pair_realGenerator_K D η := by
  rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.span_singleton_pow,
    caseII_data_pair_realGenerator_K_eq, ← caseII_etaInv_coe (K := K) η,
    ← caseII_pair_principal_ideal_eq D hp η, pow_two]
  exact Ideal.mul_mono Ideal.mul_le_left Ideal.mul_le_left

/-- **The σ-stable pair generator divided by `(ζ-1)²` is in `𝓞 K`.** Concrete element witness
of `caseII_zetaSubOne_sq_dvd_data_pair_realGenerator_K`: the quotient
`P_K / (ζ-1)² ∈ 𝓞 K`. -/
noncomputable def caseII_data_pair_realGenerator_K_div_zetaSubOne_sq
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) : 𝓞 K :=
  (caseII_zetaSubOne_sq_dvd_data_pair_realGenerator_K D hp η).choose

/-- **Defining identity of `caseII_data_pair_realGenerator_K_div_zetaSubOne_sq`.** -/
theorem caseII_data_pair_realGenerator_K_div_zetaSubOne_sq_spec
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator_K D η =
      (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 *
        caseII_data_pair_realGenerator_K_div_zetaSubOne_sq D hp η :=
  (caseII_zetaSubOne_sq_dvd_data_pair_realGenerator_K D hp η).choose_spec

/-- **`(ζ-1)² | (D.x + D.y·η)·(D.x + D.y·η⁻¹)`** restated directly in terms of the pair
product polynomial. -/
theorem caseII_zetaSubOne_sq_dvd_pair_product {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ (D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) := by
  have := caseII_zetaSubOne_sq_dvd_data_pair_realGenerator_K D hp η
  rwa [caseII_data_pair_realGenerator_K_eq] at this

/-- **`caseII_data_pair_realGenerator_K_div_zetaSubOne_sq` is σ-fixed.** The classical-choice
quotient `P_K / (ζ-1)²` need not itself be σ-fixed in general; we cannot assert it. Instead,
the equation `P_K = (ζ-1)² · (P_K / (ζ-1)²)` together with `σ(P_K) = P_K` and the σ-action on
`(ζ-1)` produces the Galois-equivariance information about the quotient. -/
theorem caseII_data_pair_realGenerator_K_eq_zeta_sub_one_sq_times_quotient
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) =
      (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 *
        caseII_data_pair_realGenerator_K_div_zetaSubOne_sq D hp η := by
  have h := caseII_data_pair_realGenerator_K_div_zetaSubOne_sq_spec D hp η
  rwa [caseII_data_pair_realGenerator_K_eq] at h

/-- **`Nonempty` form of `caseII_pair_real_caseI_form_of_realCaseIIData37`.** A direct
`Nonempty` packaging of the σ-stable Case-I-form existence: under the descent hypotheses,
there is a witness to the σ-stable Fermat-form equation `ε₁'·X^37 + ε₂'·Y^37 = Z^37` in
`𝓞 K` with σ-fixed (real) variables. Useful for downstream existence-style consumers. -/
theorem caseII_pair_real_caseI_form_of_realCaseIIData37_nonempty {m : ℕ}
    (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (hζ' : IsPrimitiveRoot (zeta_spec 37 ℚ K).toInteger 37)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hη1_ne_z : η₁ ≠ D.etaZero) (hη1inv_ne_z : caseII_etaInv η₁ ≠ D.etaZero)
    (hη2_ne_z : η₂ ≠ D.etaZero) (hη2inv_ne_z : caseII_etaInv η₂ ≠ D.etaZero)
    (hne_12 : (η₁ : 𝓞 K) ≠ (η₂ : 𝓞 K))
    (hne_1z : (η₁ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hne_2z : (η₂ : 𝓞 K) ≠ (D.etaZero : 𝓞 K))
    (hprod_12 : (η₁ : 𝓞 K) * (η₂ : 𝓞 K) ≠ 1)
    (hprod_1z : (η₁ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    (hprod_2z : (η₂ : 𝓞 K) * (D.etaZero : 𝓞 K) ≠ 1)
    {J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ₀_ne : J₀ ≠ ⊥)
    (hJ₀ : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    Nonempty (Σ' (X Y Z : 𝓞 K) (ε₁' ε₂' : (𝓞 K)ˣ),
      NumberField.IsCMField.ringOfIntegersComplexConj K X = X ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K Y = Y ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K Z = Z ∧
      (ε₁' : 𝓞 K) * X ^ 37 + (ε₂' : 𝓞 K) * Y ^ 37 = Z ^ 37) := by
  obtain ⟨X, Y, Z, ε₁', ε₂', hX, hY, hZ, heq⟩ :=
    caseII_pair_real_caseI_form_of_realCaseIIData37 D hp hζ' h_VC η₁ η₂
      hη1_ne_z hη1inv_ne_z hη2_ne_z hη2inv_ne_z
      hne_12 hne_1z hne_2z hprod_12 hprod_1z hprod_2z hJ₀_ne hJ₀
  exact ⟨X, Y, Z, ε₁', ε₂', hX, hY, hZ, heq⟩

/-- **`(ζ-1) | (D.x + D.y·η)` for any 37-th root `η`.** Direct consequence of flt-regular's
`div_zeta_sub_one_mul_zeta_sub_one`: `div_zeta_sub_one(η)·(ζ-1) = (x + y·η)`. -/
theorem caseII_zetaSubOne_dvd_x_add_y_mul {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣ (D.x + D.y * (η : 𝓞 K)) := by
  refine ⟨divZetaSubOne hp D.hζ D.equation η, ?_⟩
  have h := div_zeta_sub_one_mul_zeta_sub_one hp D.hζ D.equation η
  linear_combination -h

/-- **`(ζ-1) | (D.x + D.y·η⁻¹)` for any 37-th root `η`.** Specialization of
`caseII_zetaSubOne_dvd_x_add_y_mul` to the conjugate factor `η^36 = η⁻¹`. -/
theorem caseII_zetaSubOne_dvd_x_add_y_mul_inv {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣ (D.x + D.y * (η : 𝓞 K) ^ 36) := by
  have h := caseII_zetaSubOne_dvd_x_add_y_mul D hp (caseII_etaInv η)
  rwa [caseII_etaInv_coe] at h

/-- **`(ζ-1) | (D.x + D.y)`.** The η = 1 case of `caseII_zetaSubOne_dvd_x_add_y_mul`.
This is the basic divisibility underlying the elevated `(ζ-1)`-divisibility of the special
factor at `D.etaZero` (which has v_𝔭 = 37m+1). -/
theorem caseII_zetaSubOne_dvd_x_add_y {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣ (D.x + D.y) := by
  have h_one_mem : (1 : 𝓞 K) ∈ Polynomial.nthRootsFinset 37 (1 : 𝓞 K) :=
    (Polynomial.mem_nthRootsFinset (by norm_num) _).mpr (one_pow _)
  have h := caseII_zetaSubOne_dvd_x_add_y_mul D hp ⟨(1 : 𝓞 K), h_one_mem⟩
  simpa using h

/-- **`(ζ-1)² | (D.x + D.y)²`.** Squared form of `caseII_zetaSubOne_dvd_x_add_y`. -/
theorem caseII_zetaSubOne_sq_dvd_x_add_y_sq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ (D.x + D.y) ^ 2 :=
  pow_dvd_pow_of_dvd (caseII_zetaSubOne_dvd_x_add_y D hp) 2

/-- **Step 1:** `𝔭^m ∣ 𝔞(D.etaZero)` — direct application of `p_pow_dvd_a_eta_zero`. -/
theorem caseII_p_pow_dvd_a_etaZero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero := by
  exact p_pow_dvd_a_eta_zero hp D.hζ D.equation D.hy

/-- **Step 2:** `(𝔭^m)^37 ∣ 𝔞(D.etaZero)^37` — direct from Step 1 + `pow_dvd_pow_of_dvd`. -/
theorem caseII_p_pow_m_pow_37_dvd_a_etaZero_pow_37 {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 37 ∣
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero) ^ 37 :=
  pow_dvd_pow_of_dvd (caseII_p_pow_dvd_a_etaZero D hp) 37

set_option maxRecDepth 2000 in
/-- **Step 3-4 (combined):** `(𝔭^m)^37 ∣ 𝔠(D.etaZero)`. Bumping `maxRecDepth` for this
specific theorem to handle the elaboration of `root_div_zeta_sub_one_dvd_gcd_spec` at the
long argument list (Subtype operations from RealCaseIIData37 + D.etaZero noncomputable def). -/
theorem caseII_p_pow_m_pow_37_dvd_c_etaZero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 37 ∣
      divZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero := by
  have h_pow_dvd := caseII_p_pow_m_pow_37_dvd_a_etaZero_pow_37 D hp
  have h_spec := root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy D.etaZero
  exact dvd_trans h_pow_dvd (dvd_of_eq h_spec)

/-- **Step 5:** `(𝔭^m)^37 ∣ 𝔪 * 𝔠(D.etaZero)` — Step 4 + `Dvd.dvd.mul_left`. -/
theorem caseII_p_pow_m_pow_37_dvd_m_mul_c_etaZero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 37 ∣
      gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero :=
  (caseII_p_pow_m_pow_37_dvd_c_etaZero D hp).mul_left _

/-- **Step 6:** `(𝔭^m)^37 ∣ span{div_zeta_sub_one(D.etaZero)}` via Step 5 + the spec
`𝔪 * 𝔠 η = span{div_zeta_sub_one η}`. -/
theorem caseII_p_pow_m_pow_37_dvd_span_div_zeta_sub_one_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 37 ∣
      Ideal.span ({divZetaSubOne hp D.hζ D.equation D.etaZero} : Set (𝓞 K)) := by
  have h_step5 := caseII_p_pow_m_pow_37_dvd_m_mul_c_etaZero D hp
  have h_mc_spec := div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy D.etaZero
  exact dvd_trans h_step5 (dvd_of_eq h_mc_spec)

/-- **Step 7-8:** `(𝔭^m)^37 * 𝔭 ∣ span{D.x + D.y * D.etaZero}` via Step 6 + the element
identity `div_zeta_sub_one(D.etaZero) * (ζ-1) = D.x + D.y * D.etaZero`, combined as ideal
products: `(𝔭^m)^37 * 𝔭 ∣ span{div_zeta_sub_one(D.etaZero)} * span{ζ-1} =
span{div_zeta_sub_one(D.etaZero) * (ζ-1)} = span{D.x + D.y * D.etaZero}`. -/
theorem caseII_p_pow_m_pow_37_mul_p_dvd_span_x_add_y_mul_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 37 *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      Ideal.span ({(D.x + D.y * (D.etaZero : 𝓞 K))} : Set (𝓞 K)) := by
  have h_step6 := caseII_p_pow_m_pow_37_dvd_span_div_zeta_sub_one_etaZero D hp
  have h_elem := div_zeta_sub_one_mul_zeta_sub_one hp D.hζ D.equation D.etaZero
  have h_ideal_eq : Ideal.span
      ({divZetaSubOne hp D.hζ D.equation D.etaZero * (D.hζ.toInteger - 1)} :
        Set (𝓞 K)) =
      Ideal.span ({D.x + D.y * (D.etaZero : 𝓞 K)} : Set (𝓞 K)) := by
    congr 1
    rw [h_elem]
  have h_ideal_mul :
      Ideal.span ({divZetaSubOne hp D.hζ D.equation D.etaZero} : Set (𝓞 K)) *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) =
      Ideal.span ({divZetaSubOne hp D.hζ D.equation D.etaZero * (D.hζ.toInteger - 1)} :
        Set (𝓞 K)) :=
    Ideal.span_singleton_mul_span_singleton _ _
  refine dvd_trans (mul_dvd_mul h_step6 dvd_rfl) ?_
  rw [h_ideal_mul, h_ideal_eq]

/-- **Step 9 (ideal-level):** `𝔭^(37m+1) ∣ span{D.x + D.y * D.etaZero}` — the LTE elevated
divisibility at `D.etaZero`. Combining Step 7-8 (`(𝔭^m)^37 * 𝔭 ∣ ...`) with the power
arithmetic `(𝔭^m)^37 * 𝔭 = 𝔭^(m*37) * 𝔭 = 𝔭^(m*37+1) = 𝔭^(37m+1)` (via `pow_mul` and
`pow_succ`). -/
theorem caseII_p_pow_37m1_dvd_span_x_add_y_mul_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (37 * m + 1) ∣
      Ideal.span ({(D.x + D.y * (D.etaZero : 𝓞 K))} : Set (𝓞 K)) := by
  have h_step78 := caseII_p_pow_m_pow_37_mul_p_dvd_span_x_add_y_mul_etaZero D hp
  have h_arith : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 37 *
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) =
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (37 * m + 1) := by
    rw [← pow_mul, mul_comm m 37, pow_succ]
  rw [← h_arith]
  exact h_step78

/-- **Step 10 (element-level): `(ζ-1)^(37m+1) ∣ (D.x + D.y * D.etaZero)`** — the LTE
elevated divisibility at `D.etaZero` translated to element divisibility via
`Ideal.span_singleton_le_span_singleton` + `Ideal.dvd_iff_le` (Dedekind). -/
theorem caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) ∣ (D.x + D.y * (D.etaZero : 𝓞 K)) := by
  have h_step9 := caseII_p_pow_37m1_dvd_span_x_add_y_mul_etaZero D hp
  rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.span_singleton_pow,
    ← Ideal.dvd_iff_le]
  exact h_step9

/-- **`(ζ-1)² ∣ (D.x + D.y * D.etaZero)`** — weaker corollary of the elevated divisibility
for `m ≥ 1` (any `RealCaseIIData37`, since `one_le_m` gives `m ≥ 1`). -/
theorem caseII_zetaSubOne_sq_dvd_x_add_y_mul_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ (D.x + D.y * (D.etaZero : 𝓞 K)) := by
  have h_elev := caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp
  have h_m_pos : 1 ≤ m := D.toCaseIIData37.one_le_m
  have h_le : 2 ≤ 37 * m + 1 := by omega
  have h_pow_le : (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) :=
    pow_dvd_pow _ h_le
  exact dvd_trans h_pow_le h_elev

/-- **`(ζ-1)^(37m+1) ∣ pair_product at D.etaZero`** — direct from the elevated divisibility
at the first factor `(D.x + D.y * D.etaZero)`. -/
theorem caseII_zetaSubOne_pow_dvd_pair_product_at_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) ∣
      (D.x + D.y * (D.etaZero : 𝓞 K)) * (D.x + D.y * (D.etaZero : 𝓞 K) ^ 36) :=
  (caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp).mul_right _

/-- **`(ζ-1) ∣ (D.x + D.y * D.etaZero^36)`** — basic divisibility at the conjugate factor
of `D.etaZero`, by specialisation of `caseII_zetaSubOne_dvd_x_add_y_mul_inv`. -/
theorem caseII_zetaSubOne_dvd_x_add_y_mul_etaZero_pow_36 {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣ (D.x + D.y * (D.etaZero : 𝓞 K) ^ 36) :=
  caseII_zetaSubOne_dvd_x_add_y_mul_inv D hp D.etaZero

/-- **`(ζ-1)^(37m+2) ∣ pair_product at D.etaZero`** — combining the elevated divisibility
at the first factor (`37m+1` power) with the basic `(ζ-1)`-divisibility at the conjugate
factor. -/
theorem caseII_zetaSubOne_pow_dvd_pair_product_at_etaZero_sharper {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 2) ∣
      (D.x + D.y * (D.etaZero : 𝓞 K)) * (D.x + D.y * (D.etaZero : 𝓞 K) ^ 36) := by
  have h1 := caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp
  have h2 := caseII_zetaSubOne_dvd_x_add_y_mul_etaZero_pow_36 D hp
  have h_mul : (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) * (D.hζ.toInteger - 1 : 𝓞 K) ∣
      (D.x + D.y * (D.etaZero : 𝓞 K)) * (D.x + D.y * (D.etaZero : 𝓞 K) ^ 36) :=
    mul_dvd_mul h1 h2
  have h_pow_eq : (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 2) =
      (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) * (D.hζ.toInteger - 1 : 𝓞 K) := by
    rw [show (37 * m + 2 : ℕ) = (37 * m + 1) + 1 from rfl, pow_succ]
  rw [h_pow_eq]
  exact h_mul

/-- **The `(ζ-1)`-removed quotient of `(D.x + D.y * D.etaZero)`** at the special root. Classical
choice from `caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero`. -/
noncomputable def caseII_x_add_y_mul_etaZero_div_zetaSubOne_pow
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) : 𝓞 K :=
  (caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp).choose

/-- **Defining identity of `caseII_x_add_y_mul_etaZero_div_zetaSubOne_pow`.** -/
@[simp] theorem caseII_x_add_y_mul_etaZero_div_zetaSubOne_pow_spec
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    D.x + D.y * (D.etaZero : 𝓞 K) =
      (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) *
        caseII_x_add_y_mul_etaZero_div_zetaSubOne_pow D hp :=
  (caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp).choose_spec

/-- **σ acts on `D.x + D.y * D.etaZero` to give the conjugate factor.** Direct use of
σ-fixedness of `D.x`, `D.y` + `caseII_ringOfIntegersComplexConj_root_of_unity`. -/
theorem caseII_sigma_x_add_y_mul_etaZero {m : ℕ} (D : RealCaseIIData37 K m) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.x + D.y * (D.etaZero : 𝓞 K)) =
      D.x + D.y * (D.etaZero : 𝓞 K) ^ 36 := by
  have h_eta : (D.etaZero : 𝓞 K) ^ 37 = 1 :=
    (mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2
  rw [map_add, map_mul, D.x_real, D.y_real,
    caseII_ringOfIntegersComplexConj_root_of_unity h_eta]

/-- **σ-action on `ζ - 1`**: `σ(ζ - 1) = ζ^36 - 1`. Direct application of
`caseII_ringOfIntegersComplexConj_root_of_unity` on `ζ` plus `map_sub` and `map_one`. -/
theorem caseII_sigma_zeta_sub_one {m : ℕ} (D : RealCaseIIData37 K m) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.hζ.toInteger - 1) =
      D.hζ.toInteger ^ 36 - 1 := by
  have h_zeta_pow : D.hζ.toInteger ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  rw [map_sub, map_one, caseII_ringOfIntegersComplexConj_root_of_unity h_zeta_pow]

/-- **Element identity**: `ζ^36 - 1 = -ζ^36 * (ζ - 1)` in `𝓞 K`. Proof via the cyclotomic
identity `ζ^37 = 1`: expand RHS = `-ζ^37 + ζ^36 = -1 + ζ^36 = ζ^36 - 1`. -/
theorem caseII_zeta_pow_36_sub_one_eq {m : ℕ} (D : RealCaseIIData37 K m) :
    D.hζ.toInteger ^ 36 - 1 = -(D.hζ.toInteger ^ 36) * (D.hζ.toInteger - 1) := by
  have h_zeta_pow : D.hζ.toInteger ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  linear_combination h_zeta_pow

/-- **σ(ζ - 1) = -ζ^36 * (ζ - 1)** in `𝓞 K`. The σ-action on the cyclotomic uniformizer is
multiplication by `-ζ^36`. -/
theorem caseII_sigma_zeta_sub_one_eq_neg_zeta_pow_36_mul {m : ℕ}
    (D : RealCaseIIData37 K m) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (D.hζ.toInteger - 1) =
      -(D.hζ.toInteger ^ 36) * (D.hζ.toInteger - 1) := by
  rw [caseII_sigma_zeta_sub_one D, caseII_zeta_pow_36_sub_one_eq D]

/-- **`-ζ^36` is a unit in `𝓞 K`.** -ζ is a 2·37 = 74-th root of unity, so a unit; its 36th
power is a unit too. -/
theorem caseII_neg_zeta_pow_36_isUnit {m : ℕ} (D : RealCaseIIData37 K m) :
    IsUnit (-(D.hζ.toInteger ^ 36)) := by
  have h_zeta_unit : IsUnit (D.hζ.toInteger) :=
    D.hζ.toInteger_isPrimitiveRoot.isUnit (by norm_num)
  exact (h_zeta_unit.pow 36).neg

/-- **σ(ζ-1) is associated to (ζ-1) in `𝓞 K`.** Combines the cyclotomic unit form
`σ(ζ-1) = -ζ^36 · (ζ-1)` (`caseII_sigma_zeta_sub_one_eq_neg_zeta_pow_36_mul`) with the
unit fact `IsUnit (-ζ^36)` (`caseII_neg_zeta_pow_36_isUnit`) + `associated_unit_mul_right`. -/
theorem caseII_sigma_zeta_sub_one_associated {m : ℕ} (D : RealCaseIIData37 K m) :
    Associated (D.hζ.toInteger - 1 : 𝓞 K)
      (NumberField.IsCMField.ringOfIntegersComplexConj K (D.hζ.toInteger - 1)) := by
  rw [caseII_sigma_zeta_sub_one_eq_neg_zeta_pow_36_mul D]
  exact associated_unit_mul_right _ _ (caseII_neg_zeta_pow_36_isUnit D)

/-- **σ-equivariant elevated divisibility at the conjugate factor**:
`(ζ-1)^(37m+1) ∣ (D.x + D.y * D.etaZero^36)`. Proof via `map_dvd_iff` on the ring iso
`ringOfIntegersComplexConj K`: applying σ to the elevated divisibility at `D.etaZero` gives
`σ((ζ-1)^(37m+1)) ∣ σ(D.x + D.y * D.etaZero) = D.x + D.y * D.etaZero^36`. Then
`Associated (ζ-1)^(37m+1) σ((ζ-1)^(37m+1))` (`.pow` of the σ-action) gives the conjugate
divisibility. -/
theorem caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero_pow_36 {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) ∣ (D.x + D.y * (D.etaZero : 𝓞 K) ^ 36) := by
  have h := caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp
  set σ : 𝓞 K →+* 𝓞 K :=
    (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom with hσ_def
  have h_sigma_dvd : σ ((D.hζ.toInteger - 1) ^ (37 * m + 1)) ∣ σ (D.x + D.y * (D.etaZero : 𝓞 K)) :=
    σ.map_dvd h
  have h_sigma_rhs : σ (D.x + D.y * (D.etaZero : 𝓞 K)) = D.x + D.y * (D.etaZero : 𝓞 K) ^ 36 :=
    caseII_sigma_x_add_y_mul_etaZero D
  have h_pow_assoc : Associated ((D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1))
      (σ ((D.hζ.toInteger - 1) ^ (37 * m + 1))) := by
    rw [map_pow]
    exact (caseII_sigma_zeta_sub_one_associated D).pow_pow
  rw [h_sigma_rhs] at h_sigma_dvd
  exact h_pow_assoc.dvd.trans h_sigma_dvd

/-- **`(ζ-1)^(74m+2) ∣ pair_product at D.etaZero`** — the SHARP divisibility, combining the
elevated divisibility at BOTH conjugate factors (each `(37m+1)`-power).

This is the substantial result: the pair product `(D.x + D.y * D.etaZero) * (D.x + D.y *
D.etaZero^36)` has `(ζ-1)`-content at least `2 * (37m+1) = 74m + 2`. -/
theorem caseII_zetaSubOne_pow_dvd_pair_product_at_etaZero_sharp {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) ∣
      (D.x + D.y * (D.etaZero : 𝓞 K)) * (D.x + D.y * (D.etaZero : 𝓞 K) ^ 36) := by
  have h1 := caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp
  have h2 := caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero_pow_36 D hp
  have h_mul := mul_dvd_mul h1 h2
  have h_pow_eq : (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) *
      (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) =
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) := by
    rw [← pow_add]
    congr 1
    omega
  rwa [h_pow_eq] at h_mul

/-- **`(ζ-1)^(74m+2) ∣ caseII_data_pair_realGenerator_K D D.etaZero`** — the K-level pair
generator at the special root has elevated `(ζ-1)`-content `74m+2`. Direct corollary of
`caseII_zetaSubOne_pow_dvd_pair_product_at_etaZero_sharp` via the pair-product polynomial
identity. -/
theorem caseII_zetaSubOne_pow_dvd_pair_realGenerator_K_at_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) ∣
      caseII_data_pair_realGenerator_K D D.etaZero := by
  rw [caseII_data_pair_realGenerator_K_eq]
  exact caseII_zetaSubOne_pow_dvd_pair_product_at_etaZero_sharp D hp

/-- **The K-pair-generator at `D.etaZero` lies in `𝔭^(74m+2)`** as an `𝓞 K` element.
Translated from divisibility to ideal membership via `Ideal.span_singleton_pow` +
`Ideal.mem_span_singleton`. -/
theorem caseII_pair_realGenerator_K_at_etaZero_mem_p_pow {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator_K D D.etaZero ∈
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (74 * m + 2) := by
  have h_pow : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ (74 * m + 2) =
      Ideal.span ({((D.hζ.toInteger - 1 : 𝓞 K)) ^ (74 * m + 2)} : Set (𝓞 K)) :=
    Ideal.span_singleton_pow _ _
  rw [h_pow, Ideal.mem_span_singleton]
  exact caseII_zetaSubOne_pow_dvd_pair_realGenerator_K_at_etaZero D hp

/-- **The K⁺-uniformizer formula `(1 - ζ)·(1 - ζ^36) = 2 - (ζ + ζ^36)`** in `𝓞 K`.
This is the explicit polynomial form of the real cyclotomic uniformizer at `𝔭⁺` (Washington
GTM 83 §8.4 `λ`). The image under `σ` (= ringOfIntegersComplexConj) is itself (commutativity
of the factors), so it descends to `𝓞 K⁺`. -/
theorem caseII_one_sub_zeta_mul_one_sub_zeta_pow_36 {m : ℕ} (D : RealCaseIIData37 K m) :
    (1 - D.hζ.toInteger) * (1 - D.hζ.toInteger ^ 36) =
      2 - (D.hζ.toInteger + D.hζ.toInteger ^ 36) := by
  have h_pow : D.hζ.toInteger ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  linear_combination h_pow

/-- **The K⁺-uniformizer `(1-ζ)·(1-ζ^36) = 2 - γ_ζ` is σ-fixed.** σ swaps `(1-ζ)` and
`(1-ζ^36)`, leaving the product unchanged (commutativity). -/
theorem caseII_K_plus_uniformizer_fixed {m : ℕ} (D : RealCaseIIData37 K m) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        ((1 - D.hζ.toInteger) * (1 - D.hζ.toInteger ^ 36)) =
      (1 - D.hζ.toInteger) * (1 - D.hζ.toInteger ^ 36) := by
  have h_pow : D.hζ.toInteger ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  rw [map_mul, map_sub, map_sub, map_pow,
    caseII_ringOfIntegersComplexConj_root_of_unity h_pow]
  simp only [map_one]
  have h_pow_36_36 : (D.hζ.toInteger ^ 36) ^ 36 = D.hζ.toInteger := by
    rw [← pow_mul, show 36 * 36 = 37 * 35 + 1 by norm_num,
      pow_add, pow_mul, h_pow, one_pow, pow_one, one_mul]
  rw [h_pow_36_36]
  ring

/-- **The K⁺-uniformizer `(1-ζ)·(1-ζ^36)` descends to `𝓞 K⁺`.** Combining the σ-fixedness
(`caseII_K_plus_uniformizer_fixed`) with `ringOfIntegersComplexConj_eq_self_iff`. -/
theorem caseII_K_plus_uniformizer_descends {m : ℕ} (D : RealCaseIIData37 K m) :
    (1 - D.hζ.toInteger) * (1 - D.hζ.toInteger ^ 36) ∈
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mp
    (caseII_K_plus_uniformizer_fixed D)

/-- **The K⁺-preimage of the uniformizer `Λ := (1-ζ)(1-ζ^36)`.** -/
noncomputable def caseII_LambdaCyc {m : ℕ} (D : RealCaseIIData37 K m) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_K_plus_uniformizer_descends D).choose

/-- **Defining identity of `caseII_LambdaCyc`.** -/
@[simp] theorem caseII_LambdaCyc_spec {m : ℕ} (D : RealCaseIIData37 K m) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) =
      (1 - D.hζ.toInteger) * (1 - D.hζ.toInteger ^ 36) :=
  (caseII_K_plus_uniformizer_descends D).choose_spec

/-- **`algebraMap Λ = -ζ^36 · (ζ-1)²`** — the explicit unit-times-(ζ-1)² form of the K⁺
uniformizer's image. Proof via the cyclotomic identity `ζ^37 = 1`. -/
theorem caseII_LambdaCyc_algebraMap_eq_neg_zeta_pow_36_mul_zeta_sub_one_sq {m : ℕ}
    (D : RealCaseIIData37 K m) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) =
      -(D.hζ.toInteger ^ 36) * (D.hζ.toInteger - 1) ^ 2 := by
  rw [caseII_LambdaCyc_spec]
  have h_pow : D.hζ.toInteger ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  linear_combination (D.hζ.toInteger - 1) * h_pow

/-- **`Associated (algebraMap Λ) ((ζ-1)²)`** — the K⁺ uniformizer's image is associated to
`(ζ-1)²` via the cyclotomic unit `-ζ^36`. -/
theorem caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq {m : ℕ}
    (D : RealCaseIIData37 K m) :
    Associated
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D))
        ((D.hζ.toInteger - 1 : 𝓞 K) ^ 2) := by
  rw [caseII_LambdaCyc_algebraMap_eq_neg_zeta_pow_36_mul_zeta_sub_one_sq]
  exact associated_unit_mul_left _ _ (caseII_neg_zeta_pow_36_isUnit D)

/-- **`(algebraMap Λ)^(37m+1) ∣ caseII_data_pair_realGenerator_K D D.etaZero`** in `𝓞 K`.
Combines the Associated relation `algebraMap Λ ~ (ζ-1)²` (via the `-ζ^36` unit factor) with
the sharp divisibility `(ζ-1)^(74m+2) ∣ K-pair-gen at D.etaZero`. -/
theorem caseII_LambdaCyc_algebraMap_pow_dvd_pair_realGenerator_K_at_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D))
        ^ (37 * m + 1) ∣
      caseII_data_pair_realGenerator_K D D.etaZero := by
  have h_sharp := caseII_zetaSubOne_pow_dvd_pair_realGenerator_K_at_etaZero D hp
  have h_assoc := (caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D).pow_pow
    (n := 37 * m + 1)
  have h_pow_eq : ((D.hζ.toInteger - 1 : 𝓞 K) ^ 2) ^ (37 * m + 1) =
      (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [h_pow_eq] at h_assoc
  exact h_assoc.dvd.trans h_sharp

/-- **`Associated ((algebraMap Λ)^n) ((ζ-1)^(2n))`** — the higher-power Associated form. -/
theorem caseII_LambdaCyc_algebraMap_pow_associated_zeta_sub_one_pow_two_n {m : ℕ}
    (D : RealCaseIIData37 K m) (n : ℕ) :
    Associated
        ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D)) ^ n)
        ((D.hζ.toInteger - 1 : 𝓞 K) ^ (2 * n)) := by
  have h_pow_pair :
      ((D.hζ.toInteger - 1 : 𝓞 K) ^ 2) ^ n = (D.hζ.toInteger - 1 : 𝓞 K) ^ (2 * n) := by
    rw [← pow_mul]
  rw [← h_pow_pair]
  exact (caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D).pow_pow

/-- **`Λ ≠ 0` in `𝓞 K⁺`.** Since `algebraMap Λ = -ζ^36 · (ζ-1)^2 ≠ 0` (units, plus
`ζ - 1 ≠ 0`), and `algebraMap` is injective, `Λ ≠ 0`. -/
theorem caseII_LambdaCyc_ne_zero {m : ℕ} (D : RealCaseIIData37 K m) :
    caseII_LambdaCyc D ≠ 0 := by
  intro h_eq
  have h_alg_zero :
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) = 0 := by
    rw [h_eq, map_zero]
  rw [caseII_LambdaCyc_algebraMap_eq_neg_zeta_pow_36_mul_zeta_sub_one_sq] at h_alg_zero
  have h_zeta_ne_one : D.hζ.toInteger - 1 ≠ 0 :=
    D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37)
  have h_pow_ne : (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ≠ 0 := pow_ne_zero 2 h_zeta_ne_one
  have h_unit_ne : -(D.hζ.toInteger ^ 36 : 𝓞 K) ≠ 0 :=
    (caseII_neg_zeta_pow_36_isUnit D).ne_zero
  exact h_unit_ne (mul_left_cancel₀ h_pow_ne (by
    rw [mul_zero]; linear_combination h_alg_zero))

/-- **`(algebraMap Λ) ≠ 0` in `𝓞 K`.** Immediate from `caseII_LambdaCyc_ne_zero` +
algebraMap injectivity. -/
theorem caseII_LambdaCyc_algebraMap_ne_zero {m : ℕ} (D : RealCaseIIData37 K m) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) ≠ 0 := by
  intro h
  exact caseII_LambdaCyc_ne_zero D
    ((FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
      (by rw [h]; simp))

/-- **K⁺-level divisibility: `Λ^(37m+1) ∣ caseII_data_pair_realGenerator D D.etaZero`** in
`𝓞 K⁺`. Derived from K-level divisibility by extracting the σ-fixed quotient. -/
theorem caseII_LambdaCyc_pow_dvd_pair_realGenerator_at_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_LambdaCyc D ^ (37 * m + 1) ∣ caseII_data_pair_realGenerator D D.etaZero := by
  obtain ⟨c, hc⟩ := caseII_LambdaCyc_algebraMap_pow_dvd_pair_realGenerator_K_at_etaZero D hp
  unfold caseII_data_pair_realGenerator_K at hc
  have h_alg_Lambda_pow_fixed :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          ((algebraMap _ (𝓞 K) (caseII_LambdaCyc D)) ^ (37 * m + 1)) =
        (algebraMap _ (𝓞 K) (caseII_LambdaCyc D)) ^ (37 * m + 1) := by
    rw [map_pow]
    congr 1
    exact caseII_algebraMap_of_descended_real_is_fixed _
  have h_alg_pair_fixed :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap _ (𝓞 K) (caseII_data_pair_realGenerator D D.etaZero)) =
        algebraMap _ (𝓞 K) (caseII_data_pair_realGenerator D D.etaZero) :=
    caseII_algebraMap_of_descended_real_is_fixed _
  have hc_sigma := congrArg (NumberField.IsCMField.ringOfIntegersComplexConj K) hc
  rw [map_mul, h_alg_Lambda_pow_fixed, h_alg_pair_fixed] at hc_sigma
  have h_pow_ne :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D))
          ^ (37 * m + 1) ≠ 0 :=
    pow_ne_zero _ (caseII_LambdaCyc_algebraMap_ne_zero D)
  have h_c_sigma :
      NumberField.IsCMField.ringOfIntegersComplexConj K c = c := by
    have : (algebraMap _ (𝓞 K) (caseII_LambdaCyc D)) ^ (37 * m + 1) *
        NumberField.IsCMField.ringOfIntegersComplexConj K c =
      (algebraMap _ (𝓞 K) (caseII_LambdaCyc D)) ^ (37 * m + 1) * c := by
      rw [← hc_sigma, hc]
    exact mul_left_cancel₀ h_pow_ne this
  obtain ⟨d, hd⟩ :=
    (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) c).mp h_c_sigma
  refine ⟨d, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [map_mul, map_pow, hd]
  exact hc

/-- **Concrete witness:** the quotient `K⁺-pair-gen at D.etaZero / Λ^(37m+1)` as an
explicit `𝓞 K⁺` element, via classical choice from
`caseII_LambdaCyc_pow_dvd_pair_realGenerator_at_etaZero`. -/
noncomputable def caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_LambdaCyc_pow_dvd_pair_realGenerator_at_etaZero D hp).choose

/-- **Defining identity of `caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow`.** -/
@[simp] theorem caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow_spec
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator D D.etaZero =
      caseII_LambdaCyc D ^ (37 * m + 1) *
        caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp :=
  (caseII_LambdaCyc_pow_dvd_pair_realGenerator_at_etaZero D hp).choose_spec

/-- **K⁺-ideal-level: `span{Λ}^(37m+1) ∣ span{K⁺-pair-gen at D.etaZero}`** in `𝓞 K⁺`. -/
theorem caseII_LambdaCyc_pow_span_dvd_span_pair_realGenerator_at_etaZero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({caseII_LambdaCyc D} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ^ (37 * m + 1) ∣
      Ideal.span ({caseII_data_pair_realGenerator D D.etaZero} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) := by
  have h := caseII_LambdaCyc_pow_dvd_pair_realGenerator_at_etaZero D hp
  rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.span_singleton_pow,
    ← Ideal.dvd_iff_le] at h
  exact h

/-- **`(algebraMap Λ) ∣ caseII_data_pair_realGenerator_K D η`** for any η: the K⁺ uniformizer's
algebraMap divides the K-pair-generator at any root, because the K-pair-generator has
`(ζ-1)²` content (`caseII_zetaSubOne_sq_dvd_data_pair_realGenerator_K`) and `algebraMap Λ` is
associated to `(ζ-1)²`. -/
theorem caseII_LambdaCyc_algebraMap_dvd_pair_realGenerator_K {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) ∣
      caseII_data_pair_realGenerator_K D η := by
  have h_dvd : (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ caseII_data_pair_realGenerator_K D η :=
    caseII_zetaSubOne_sq_dvd_data_pair_realGenerator_K D hp η
  have h_assoc := caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D
  exact h_assoc.dvd.trans h_dvd

/-- **`Λ ∣ caseII_data_pair_realGenerator D η`** for any η in `𝓞 K⁺`. K⁺-level Λ-divisibility
of the pair generator at any root. Lifts from K-level via σ-fixed quotient extraction
(same pattern as `caseII_LambdaCyc_pow_dvd_pair_realGenerator_at_etaZero`). -/
theorem caseII_LambdaCyc_dvd_pair_realGenerator {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_LambdaCyc D ∣ caseII_data_pair_realGenerator D η := by
  obtain ⟨c, hc⟩ := caseII_LambdaCyc_algebraMap_dvd_pair_realGenerator_K D hp η
  unfold caseII_data_pair_realGenerator_K at hc
  have h_alg_Lambda_fixed :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap _ (𝓞 K) (caseII_LambdaCyc D)) =
        algebraMap _ (𝓞 K) (caseII_LambdaCyc D) :=
    caseII_algebraMap_of_descended_real_is_fixed _
  have h_alg_pair_fixed :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap _ (𝓞 K) (caseII_data_pair_realGenerator D η)) =
        algebraMap _ (𝓞 K) (caseII_data_pair_realGenerator D η) :=
    caseII_algebraMap_of_descended_real_is_fixed _
  have hc_sigma := congrArg (NumberField.IsCMField.ringOfIntegersComplexConj K) hc
  rw [map_mul, h_alg_Lambda_fixed, h_alg_pair_fixed] at hc_sigma
  have h_Lambda_ne : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
      (caseII_LambdaCyc D) ≠ 0 := caseII_LambdaCyc_algebraMap_ne_zero D
  have h_c_sigma :
      NumberField.IsCMField.ringOfIntegersComplexConj K c = c := by
    have : algebraMap _ (𝓞 K) (caseII_LambdaCyc D) *
        NumberField.IsCMField.ringOfIntegersComplexConj K c =
      algebraMap _ (𝓞 K) (caseII_LambdaCyc D) * c := by
      rw [← hc_sigma, hc]
    exact mul_left_cancel₀ h_Lambda_ne this
  obtain ⟨d, hd⟩ :=
    (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) c).mp h_c_sigma
  refine ⟨d, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [map_mul, hd]
  exact hc

/-- **Concrete witness for the Λ-divisibility at any η.** -/
noncomputable def caseII_pair_realGenerator_div_LambdaCyc {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_LambdaCyc_dvd_pair_realGenerator D hp η).choose

/-- **Defining identity of `caseII_pair_realGenerator_div_LambdaCyc`.** -/
@[simp] theorem caseII_pair_realGenerator_div_LambdaCyc_spec
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator D η =
      caseII_LambdaCyc D * caseII_pair_realGenerator_div_LambdaCyc D hp η :=
  (caseII_LambdaCyc_dvd_pair_realGenerator D hp η).choose_spec

/-- **K⁺-level ideal membership**: `K⁺-pair-gen at D.etaZero ∈ span{Λ}^(37m+1)`. -/
theorem caseII_pair_realGenerator_at_etaZero_mem_LambdaCyc_pow_ideal {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator D D.etaZero ∈
      Ideal.span ({caseII_LambdaCyc D} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ^ (37 * m + 1) := by
  have h := caseII_LambdaCyc_pow_dvd_pair_realGenerator_at_etaZero D hp
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h

/-- **K⁺-level ideal membership for any η**: `K⁺-pair-gen at η ∈ span{Λ}`. -/
theorem caseII_pair_realGenerator_mem_LambdaCyc_ideal {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator D η ∈
      Ideal.span ({caseII_LambdaCyc D} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) := by
  rw [Ideal.mem_span_singleton]
  exact caseII_LambdaCyc_dvd_pair_realGenerator D hp η

/-- **The K⁺-pair-generator at `D.etaZero` is nonzero** in `𝓞 K⁺` (from
`caseII_data_pair_realGenerator_ne_zero`, specialised). -/
theorem caseII_data_pair_realGenerator_at_etaZero_ne_zero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator D D.etaZero ≠ 0 :=
  caseII_data_pair_realGenerator_ne_zero D hp D.etaZero

/-- **The K⁺ Λ-quotient at `D.etaZero` is nonzero** — from the equation
`K⁺-pair-gen = Λ^(37m+1) * quotient`, with `K⁺-pair-gen ≠ 0` and `Λ ≠ 0`. -/
theorem caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow_ne_zero
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp ≠ 0 := by
  intro h_zero
  have h_pair_ne : caseII_data_pair_realGenerator D D.etaZero ≠ 0 :=
    caseII_data_pair_realGenerator_at_etaZero_ne_zero D hp
  apply h_pair_ne
  rw [caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow_spec D hp, h_zero, mul_zero]

/-- **Cleanest packaging: existence of Λ-divisibility witness for `K⁺-pair-gen at D.etaZero`.**
For any `RealCaseIIData37 D` with `hp`, there exist `quotient ∈ 𝓞 K⁺` nonzero such that
`K⁺-pair-gen at D.etaZero = Λ^(37m+1) * quotient`. -/
theorem caseII_pair_realGenerator_at_etaZero_exists_LambdaCyc_decomposition {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    ∃ q : 𝓞 (NumberField.maximalRealSubfield K), q ≠ 0 ∧
      caseII_data_pair_realGenerator D D.etaZero =
        caseII_LambdaCyc D ^ (37 * m + 1) * q :=
  ⟨caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp,
    caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow_ne_zero D hp,
    caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow_spec D hp⟩

/-- **`Ideal.span{K⁺-pair-gen at D.etaZero} = (Ideal.span{Λ})^(37m+1) · Ideal.span{quotient}`**
in `𝓞 K⁺`. The principal-ideal factorization of the K⁺-pair-generator at the special root. -/
theorem caseII_pair_realGenerator_at_etaZero_span_eq_LambdaCyc_pow_mul_quotient
    {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({caseII_data_pair_realGenerator D D.etaZero} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) =
      Ideal.span ({caseII_LambdaCyc D} : Set _) ^ (37 * m + 1) *
        Ideal.span ({caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp} : Set _) := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  congr 1
  congr 1
  exact caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow_spec D hp

/-- **The σ-stable pair-product descent existence (the satisfiable replacement for
`CaseIIRealIdealDescent37`).** For each `RealCaseIIData37 D`, root `η ≠ D.etaZero` with
`caseII_etaInv η ≠ D.etaZero`, there exists `J : Ideal 𝓞 K⁺` with `J ≠ ⊥` such that
`J.map = 𝔞(η)·𝔞(η⁻¹)`. Immediate from `caseII_sigma_stable_ideal_descends`
(`CaseII/RealGenerator.lean`). This is the σ-stable target that REPLACES the unsatisfiable
raw quotient form of `CaseIIRealIdealDescent37`. -/
theorem caseII_sigma_stable_pair_descent_exists {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero) :
    ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
      J ≠ ⊥ ∧
      J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
  obtain ⟨J, hJ⟩ := caseII_sigma_stable_ideal_descends D hp η hη hηinv
  have hJ_ne : J ≠ ⊥ := fun h_eq => by
    rw [h_eq, Ideal.map_bot] at hJ
    have h_mul_eq_bot :
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) = ⊥ := hJ.symm
    rw [Ideal.mul_eq_bot] at h_mul_eq_bot
    rcases h_mul_eq_bot with h | h
    · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η h
    · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η) h
  exact ⟨J, hJ_ne, hJ⟩

/-- **Satisfiable σ-stable target restated as `Nonempty`-form**, packaging
`caseII_sigma_stable_pair_descent_exists` as the data record needed by the FLT37 endpoint's
`CaseIIRealIdealDescent37`-replacement rewire. For each `RealCaseIIData37 D` and σ-stable
test pair `(η, η⁻¹)` (both ≠ D.etaZero), provides a nonzero ideal `J ∈ 𝓞 K⁺` with the
σ-stable pair-product `.map` identity. -/
theorem caseII_sigma_stable_pair_descent_nonempty {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero) :
    Nonempty (Σ' (J : Ideal (𝓞 (NumberField.maximalRealSubfield K))),
      (J ≠ ⊥) ×' (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))) := by
  obtain ⟨J, hJ_ne, hJ⟩ := caseII_sigma_stable_pair_descent_exists D hp η hη hηinv
  exact ⟨J, hJ_ne, hJ⟩

/-- **K⁺-Λ-Pair-Descent**: existence packaging combining `caseII_sigma_stable_pair_descent_exists`
with the Λ-divisibility of the K⁺-pair-generator. For each `RealCaseIIData37 D` and test pair
`(η, η⁻¹)` with η, η⁻¹ ≠ D.etaZero, there exist ideal `J ≠ ⊥` in `𝓞 K⁺` realizing the σ-stable
pair product, and a `𝓞 K⁺` element `a` (= `caseII_data_pair_realGenerator D η`) Λ-divisible. -/
theorem caseII_K_plus_Lambda_pair_descent_exists {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero) :
    ∃ (J : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
      (a : 𝓞 (NumberField.maximalRealSubfield K)),
      J ≠ ⊥ ∧
      J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ∧
      caseII_LambdaCyc D ∣ a := by
  obtain ⟨J, hJ_ne, hJ⟩ := caseII_sigma_stable_pair_descent_exists D hp η hη hηinv
  refine ⟨J, caseII_data_pair_realGenerator D η, hJ_ne, hJ, ?_⟩
  exact caseII_LambdaCyc_dvd_pair_realGenerator D hp η

/-- **σ-equivariant form of `caseII_sigma_stable_pair_descent_exists`.** The σ-stable pair
product is symmetric under `η ↔ η⁻¹`: `𝔞(η)·𝔞(η⁻¹) = 𝔞(η⁻¹)·𝔞(η)`, so the descended `J`
applies equivalently for the inverse root. -/
theorem caseII_sigma_stable_pair_descent_exists_etaInv {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero) :
    ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
      J ≠ ⊥ ∧
      J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
            (caseII_etaInv (caseII_etaInv η)) := by
  rw [caseII_etaInv_etaInv]
  obtain ⟨J, hJ_ne, hJ⟩ := caseII_sigma_stable_pair_descent_exists D hp η hη hηinv
  refine ⟨J, hJ_ne, ?_⟩
  rw [hJ, mul_comm]

/-- **The satisfiable σ-stable anchored real-generator existence form.** For a real Case-II
datum `D`, a σ-stable test pair `(η, η⁻¹)` (with both ≠ D.etaZero), an anchor descent ideal
`J₀ ≠ ⊥` realising `J₀.map = 𝔞(η₀)·𝔞(η₀⁻¹)`, and the K⁺-class-group VC hypothesis `h_VC`,
there exist real `x, y ∈ 𝓞 K⁺` (nonzero) with the σ-stable anchored cross identity in `𝓞 K`:
`(algebraMap x) · (𝔞(η)·𝔞(η⁻¹)) = (algebraMap y) · (𝔞(η₀)·𝔞(η₀⁻¹))`. This is the satisfiable
replacement target for the unsatisfiable raw quotient `𝔞(η)/𝔞₀`, obtained by composing
the σ-stable J descent (`caseII_sigma_stable_pair_descent_exists`), the descended class
equality (`caseII_descended_anchored_class_eq`), and the cross-multiplication packaging
(`caseII_sigma_stable_anchored_real_identity`). -/
theorem caseII_sigma_stable_anchored_real_generator_exists {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero)
    {J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ0_ne : J₀ ≠ ⊥)
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    ∃ (x y : 𝓞 (NumberField.maximalRealSubfield K)), x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x} *
          (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) =
        Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y} *
          (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
              (caseII_etaInv D.etaZero)) := by
  obtain ⟨J, hJ_ne, hJ⟩ := caseII_sigma_stable_pair_descent_exists D hp η hη hηinv
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    caseII_descended_anchored_real_generators D hp h_VC η hJ_ne hJ0_ne hJ hJ0
  refine ⟨x, y, hx, hy, ?_⟩
  exact caseII_sigma_stable_anchored_real_identity D hp η hJ hJ0 hxy

/-- **The satisfiable σ-stable anchored real-generator data record.** Data version of
`caseII_sigma_stable_anchored_real_generator_exists`: bundles the pair `(xPlus, yPlus)`
in `𝓞 K⁺` (both nonzero) with the σ-stable cross identity at the test pair `(η, η⁻¹)`
against the anchor pair `(η₀, η₀⁻¹)`. This is the satisfiable replacement target for the
unsatisfiable raw quotient `𝔞(η)/𝔞₀`, matching the reviewer's option B (σ-stable target on
`RealCaseIIData37`). -/
structure CaseIISigmaPairAnchoredFixedGenerator37 {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) where
  xPlus : 𝓞 (NumberField.maximalRealSubfield K)
  yPlus : 𝓞 (NumberField.maximalRealSubfield K)
  xPlus_ne_zero : xPlus ≠ 0
  yPlus_ne_zero : yPlus ≠ 0
  cross_eq :
    Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) xPlus} *
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) =
      Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) yPlus} *
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
            (caseII_etaInv D.etaZero))

/-- **Constructor for `CaseIISigmaPairAnchoredFixedGenerator37`** from a real Case-II datum,
the K⁺-class-group VC hypothesis, and an anchor descent ideal. The constructor exposes the
satisfiable σ-stable target as a data record (rather than an existence proposition), suitable
for consumption by the rewired Washington 9.4 source. -/
noncomputable def caseII_sigma_pair_anchored_fixedGenerator_of_realIdealModel {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero)
    {J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ0_ne : J₀ ≠ ⊥)
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    CaseIISigmaPairAnchoredFixedGenerator37 D hp η := by
  have H := caseII_sigma_stable_anchored_real_generator_exists D hp h_VC η hη hηinv hJ0_ne hJ0
  exact
    { xPlus := H.choose
      yPlus := H.choose_spec.choose
      xPlus_ne_zero := H.choose_spec.choose_spec.1
      yPlus_ne_zero := H.choose_spec.choose_spec.2.1
      cross_eq := H.choose_spec.choose_spec.2.2 }

/-- **K⁺-uniformizer Λ spans 𝔭² in K.** As an ideal of `𝓞 K`,
`(span{Λ}).map(algebraMap) = span{(ζ-1)²}`. This is the K-level form of the K⁺/K
ramification formula at the prime over 37: with `Λ = (1-ζ)(1-ζ^36) ∈ 𝓞 K⁺` and
`𝔭 = (ζ-1)·𝓞 K = (1-ζ^36)·𝓞 K` (the totally ramified K-prime over 37), `Λ·𝓞 K = 𝔭²`.
Used in the anchor-descent argument for σ-stable pair products at η = D.etaZero. -/
theorem caseII_LambdaCyc_span_map_eq_zetaSubOne_sq_span {m : ℕ} (D : RealCaseIIData37 K m) :
    (Ideal.span ({caseII_LambdaCyc D} : Set (𝓞 (NumberField.maximalRealSubfield K)))).map
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K) ^ 2} : Set (𝓞 K)) := by
  rw [Ideal.map_span, Set.image_singleton]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    (caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D)

/-- **`(span{Λ}^k).map = 𝔭^(2k)`.** Iterated form of
`caseII_LambdaCyc_span_map_eq_zetaSubOne_sq_span`:
the K⁺-ideal `(Λ)^k` extends to `𝔭^(2k)` in K. -/
theorem caseII_LambdaCyc_pow_span_map_eq_zetaSubOne_pow_span {m : ℕ}
    (D : RealCaseIIData37 K m) (k : ℕ) :
    ((Ideal.span ({caseII_LambdaCyc D} : Set (𝓞 (NumberField.maximalRealSubfield K)))) ^ k).map
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K) ^ (2 * k)} : Set (𝓞 K)) := by
  rw [Ideal.map_pow, caseII_LambdaCyc_span_map_eq_zetaSubOne_sq_span, ← Ideal.span_singleton_pow,
    ← pow_mul]
  rw [show 2 * k = k * 2 from Nat.mul_comm 2 k, Ideal.span_singleton_pow]

/-- **Adjacent pair of σ-stable anchored real-generator data records.** Bundles the two
`CaseIISigmaPairAnchoredFixedGenerator37` data records at `D.etaOne` and `D.etaTwo` (the
two adjacent test roots used by Washington 9.4). This is the satisfiable σ-stable
replacement for `CaseIIWashingtonAdjacentFixedIntegralGenerators37`. -/
structure CaseIISigmaPairAnchoredAdjacentFixedGenerators37 {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) where
  atEtaOne : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne
  atEtaTwo : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo

/-- **Constructor for the adjacent σ-stable pair-generator record.** From a real Case-II datum,
the K⁺-VC hypothesis, and an anchor descent J₀, produces the pair of σ-stable adjacent
generator records. Calls `caseII_sigma_pair_anchored_fixedGenerator_of_realIdealModel` twice
at D.etaOne and D.etaTwo. Requires the η₁⁻¹, η₂⁻¹ ≠ D.etaZero side-conditions
(both adjacent test pair roots remain non-anchor under inversion). -/
noncomputable def caseII_sigma_pair_anchored_adjacent_of_realIdealModel {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (hη1inv : caseII_etaInv D.etaOne ≠ D.etaZero)
    (hη2inv : caseII_etaInv D.etaTwo ≠ D.etaZero)
    {J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ0_ne : J₀ ≠ ⊥)
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    CaseIISigmaPairAnchoredAdjacentFixedGenerators37 D hp where
  atEtaOne :=
    caseII_sigma_pair_anchored_fixedGenerator_of_realIdealModel D hp h_VC D.etaOne
      D.toCaseIIData37.etaOne_ne_etaZero hη1inv hJ0_ne hJ0
  atEtaTwo :=
    caseII_sigma_pair_anchored_fixedGenerator_of_realIdealModel D hp h_VC D.etaTwo
      D.toCaseIIData37.etaTwo_ne_etaZero hη2inv hJ0_ne hJ0

/-- **The Case-II II1 satisfiable σ-stable source for FLT37.** For each real Case-II datum
`D : RealCaseIIData37 K m` and adjacent root `η ∈ {D.etaOne, D.etaTwo}`, an explicit
`CaseIISigmaPairAnchoredFixedGenerator37` data record (the satisfiable σ-stable target
replacing the unsatisfiable raw quotient `𝔞(η)/𝔞₀` of the original
`CaseIIRealIdealDescent37`). Provided by composing the anchor-descent J₀ existence (currently
exposed as a parametric input) with the K⁺-VC hypothesis discharge via Sinnott. This is the
producer-side packaging that the rewired Washington 9.4 descent step will consume. -/
def CaseIISigmaPairAnchoredSource37 [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Type :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    caseII_etaInv D.etaOne ≠ D.etaZero →
    caseII_etaInv D.etaTwo ≠ D.etaZero →
    CaseIISigmaPairAnchoredAdjacentFixedGenerators37 D (by decide : (37 : ℕ) ≠ 2)

/-- **The anchor pair product is nonzero as a fractional ideal.** Both factors
`𝔞(η₀)` and `𝔞(η₀⁻¹)` are nonzero `𝓞 K`-ideals (`caseII_rootIdeal_ne_bot`), so their
product is nonzero, so its coercion to `FractionalIdeal (𝓞 K)⁰ K` is nonzero. -/
theorem caseII_anchor_pair_frac_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
          (caseII_etaInv D.etaZero) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  intro h
  rcases Ideal.mul_eq_bot.mp h with h | h
  · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero h
  · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv D.etaZero) h

/-- **σ-stable cross identity expressed as a fractional-ideal ratio identity.** From a
σ-stable anchored generator record, the K-level fractional-ideal ratio of the test
pair product to the anchor pair product is the principal `spanSingleton` generated by
the real ratio `(algebraMap y) / (algebraMap x)`. This is the K-fractional form used
to bridge into the raw-quotient principal form needed by the existing Diekmann
descent step (`exists_solution'_of_etaZeroSpanSingletons`). -/
theorem caseII_sigma_pair_anchored_fractional_ratio {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus)) *
        ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) :
          Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus)) *
        ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
              (caseII_etaInv D.etaZero) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hint := G.cross_eq
  have h := congrArg (fun I : Ideal (𝓞 K) => (↑I : FractionalIdeal (𝓞 K)⁰ K)) hint
  simpa only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] using h

/-- **σ-stable principal ratio: test pair / anchor pair = spanSingleton(real ratio).**
Dividing both sides of `caseII_sigma_pair_anchored_fractional_ratio` by the (nonzero)
`spanSingleton(algebraMap x)` and the anchor pair product gives the K-fractional-ideal
principal-ratio form. -/
theorem caseII_sigma_pair_anchored_principal_ratio {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) :
        Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) /
        ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
              (caseII_etaInv D.etaZero) : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        ((algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus)) /
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus))) := by
  have h_xPlus_K_ne_zero :
      algebraMap (𝓞 K) K
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _
        (FaithfulSMul.algebraMap_injective (𝓞 K) K),
      map_eq_zero_iff _
        (FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))]
    exact G.xPlus_ne_zero
  have h_anchor_ne_zero := caseII_anchor_pair_frac_ne_zero D hp
  have h_spanX_ne_zero : FractionalIdeal.spanSingleton (𝓞 K)⁰
      (algebraMap (𝓞 K) K
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus)) ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff (R := 𝓞 K) (P := K)).mpr h_xPlus_K_ne_zero
  have hcross := caseII_sigma_pair_anchored_fractional_ratio D hp η G
  rw [show FractionalIdeal.spanSingleton (𝓞 K)⁰
      ((algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus)) /
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus))) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus)) /
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus)) from
    (FractionalIdeal.spanSingleton_div_spanSingleton K _ _).symm]
  rw [div_eq_div_iff h_anchor_ne_zero h_spanX_ne_zero, mul_comm]
  exact hcross

/-- **`𝔭^m ∣ 𝔞(caseII_etaInv D.etaZero)`.** σ-symmetric companion of `caseII_p_pow_dvd_a_etaZero`:
since `σ(𝔞(D.etaZero)) = 𝔞(caseII_etaInv D.etaZero)` (`RealCaseIIData37.map_rootIdeal`),
and `σ` fixes the prime `𝔭 = span{ζ-1}` (`σ(ζ-1) = ζ^36 - 1` is associated to `(ζ-1)`),
applying `σ` to `𝔭^m ∣ 𝔞(D.etaZero)` gives `𝔭^m ∣ 𝔞(caseII_etaInv D.etaZero)`. This is the
analog of `p_pow_dvd_a_eta_zero` for the conjugate root, used in the σ-stable anchor
descent argument. -/
theorem caseII_p_pow_dvd_a_caseII_etaInv_etaZero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (caseII_etaInv D.etaZero) := by
  have h_orig := caseII_p_pow_dvd_a_etaZero D hp
  have h_le : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero ≤
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m :=
    Ideal.dvd_iff_le.mp h_orig
  have h_map_le :
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≤
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :=
    Ideal.map_mono h_le
  have h_sigma_dvd : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom ∣
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :=
    Ideal.dvd_iff_le.mpr h_map_le
  rw [RealCaseIIData37.map_rootIdeal D hp D.etaZero] at h_sigma_dvd
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h_sigma_dvd
  rwa [show Ideal.span ({(NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom
          (D.hζ.toInteger - 1)} : Set (𝓞 K)) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) from ?_] at h_sigma_dvd
  · exact Ideal.span_singleton_eq_span_singleton.mpr
      (caseII_sigma_zeta_sub_one_associated D).symm

/-- **`𝔭^(2m) ∣ 𝔞(D.etaZero)·𝔞(caseII_etaInv D.etaZero)`.** Pair product 𝔭-content lower
bound: from `𝔭^m ∣ 𝔞(D.etaZero)` (`caseII_p_pow_dvd_a_etaZero`) and the σ-conjugate
`𝔭^m ∣ 𝔞(caseII_etaInv D.etaZero)` (`caseII_p_pow_dvd_a_caseII_etaInv_etaZero`), the
product `𝔭^(2m)` divides the pair product. The 2m-multiplicity is *even*, so descends
to `(span Λ)^m` in `𝓞 K⁺` (via the K⁺/K ramification formula
`span Λ . map = span (ζ-1)²`). -/
theorem caseII_p_pow_two_m_dvd_pair_at_etaZero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
          (caseII_etaInv D.etaZero) := by
  rw [two_mul, pow_add]
  exact mul_dvd_mul (caseII_p_pow_dvd_a_etaZero D hp)
    (caseII_p_pow_dvd_a_caseII_etaInv_etaZero D hp)

/-- **The 𝔭-coprime part of the anchor pair product.** Concrete witness for the
divisibility `𝔭^(2m) ∣ 𝔞(η₀)·𝔞(η₀⁻¹)`: the quotient ideal whose product with `𝔭^(2m)`
gives the pair product. -/
noncomputable def caseII_anchor_pair_div_p_pow_two_m {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) : Ideal (𝓞 K) :=
  (caseII_p_pow_two_m_dvd_pair_at_etaZero D hp).choose

/-- **Defining spec of `caseII_anchor_pair_div_p_pow_two_m`.** -/
theorem caseII_anchor_pair_div_p_pow_two_m_spec {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
          (caseII_etaInv D.etaZero) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) *
        caseII_anchor_pair_div_p_pow_two_m D hp :=
  (caseII_p_pow_two_m_dvd_pair_at_etaZero D hp).choose_spec

/-- **The 𝔭-coprime part of the anchor pair product is nonzero.** Since `𝔭^(2m)·Q = pair`
and the pair is nonzero (product of two nonzero ideals), `𝔭^(2m)` is nonzero, so `Q ≠ 0`
by the product rule for ideals. -/
theorem caseII_anchor_pair_div_p_pow_two_m_ne_bot {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    caseII_anchor_pair_div_p_pow_two_m D hp ≠ ⊥ := by
  intro h
  have h_pair_ne :
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
          (caseII_etaInv D.etaZero) ≠ ⊥ := by
    intro hp_eq
    rcases Ideal.mul_eq_bot.mp hp_eq with h | h
    · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero h
    · exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv D.etaZero) h
  have h_spec := caseII_anchor_pair_div_p_pow_two_m_spec D hp
  rw [h, Ideal.mul_bot] at h_spec
  exact h_pair_ne h_spec

/-- **σ-fixedness of the 𝔭-coprime part.** Applying σ to `pair = 𝔭^(2m)·Q` gives
`σ(pair) = σ(𝔭)^(2m) · σ(Q)`. With `σ(pair) = pair` (`RealCaseIIData37.map_rootIdeal_mul_conj`)
and `σ(𝔭) ∼ 𝔭` (associated, hence equal as spans), we get `pair = 𝔭^(2m) · σ(Q)`.
By Dedekind-domain cancellation (the 𝓞 K is a UFM at the ideal level and `𝔭^(2m) ≠ 0`),
`Q = σ(Q)`. -/
theorem caseII_anchor_pair_div_p_pow_two_m_sigma_fixed {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (caseII_anchor_pair_div_p_pow_two_m D hp).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      caseII_anchor_pair_div_p_pow_two_m D hp := by
  have h_spec := caseII_anchor_pair_div_p_pow_two_m_spec D hp
  set σ : 𝓞 K →+* 𝓞 K :=
    (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom with hσ_def
  have h_sigma_spec : (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
          (caseII_etaInv D.etaZero)).map σ =
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) *
        caseII_anchor_pair_div_p_pow_two_m D hp).map σ :=
    congrArg (Ideal.map σ) h_spec
  rw [show (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
          (caseII_etaInv D.etaZero)).map σ = _ from
    RealCaseIIData37.map_rootIdeal_mul_conj D hp D.etaZero] at h_sigma_spec
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h_sigma_spec
  rw [show Ideal.span ({σ (D.hζ.toInteger - 1)} : Set (𝓞 K)) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) from
    Ideal.span_singleton_eq_span_singleton.mpr
      (caseII_sigma_zeta_sub_one_associated D).symm] at h_sigma_spec
  rw [h_spec] at h_sigma_spec
  have h_p_ne_bot :
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥ := by
    exact p_ne_zero D.hζ
  have h_p_pow_ne_bot :
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m)) ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot] at h_p_ne_bot ⊢
    exact pow_ne_zero _ h_p_ne_bot
  exact (mul_left_cancel₀ h_p_pow_ne_bot h_sigma_spec).symm

/-- **σ-conjugate of `a_eta_zero_dvd_p_pow_spec`.** The 𝔭-coprime part of `𝔞(caseII_etaInv η₀)`
is `(aEtaZeroDvdPPow).map σ`, satisfying `𝔭^m · (aEtaZeroDvdPPow).map σ =
𝔞(caseII_etaInv η₀)`. Obtained by applying σ to the original `a_eta_zero_dvd_p_pow_spec` and
simplifying via `σ(𝔭) = 𝔭` and `σ(𝔞(η₀)) = 𝔞(caseII_etaInv η₀)`. -/
theorem caseII_a_etaInv_dvd_p_pow_spec {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m *
        (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (caseII_etaInv D.etaZero) := by
  have h_orig := a_eta_zero_dvd_p_pow_spec hp D.hζ D.equation D.hy
  have h_sigma := congrArg (Ideal.map
    (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) h_orig
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h_sigma
  rw [show Ideal.span
      ({(NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom
          (D.hζ.toInteger - 1)} : Set (𝓞 K)) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) from
    Ideal.span_singleton_eq_span_singleton.mpr
      (caseII_sigma_zeta_sub_one_associated D).symm] at h_sigma
  -- Both proofs of (37 : ℕ) ≠ 2 are propositionally equal; rewrite hp to D.etaZero's form:
  have h_map := RealCaseIIData37.map_rootIdeal D hp D.etaZero
  simp only [CaseIIData37.etaZero] at h_map
  rwa [h_map] at h_sigma

/-- **Q identification: `Q = 𝔞₀ · σ(𝔞₀)`.** The 𝔭-coprime quotient of the anchor pair
product equals the product of the 𝔭-coprime parts of `𝔞(η₀)` and `𝔞(caseII_etaInv η₀)`.
Combine `pair = 𝔭^(2m) · Q` and `pair = (𝔭^m · 𝔞₀) · (𝔭^m · σ(𝔞₀)) = 𝔭^(2m) · (𝔞₀ · σ(𝔞₀))`
and cancel `𝔭^(2m) ≠ ⊥`. -/
theorem caseII_anchor_pair_div_p_pow_two_m_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    caseII_anchor_pair_div_p_pow_two_m D hp =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy *
        (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  have h_spec := caseII_anchor_pair_div_p_pow_two_m_spec D hp
  have h_first := a_eta_zero_dvd_p_pow_spec hp D.hζ D.equation D.hy
  have h_sigma := caseII_a_etaInv_dvd_p_pow_spec D hp
  have h_via_product :
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
            (caseII_etaInv D.etaZero) =
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) *
          (aEtaZeroDvdPPow hp D.hζ D.equation D.hy *
            (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
              (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) := by
    have hLHS_eq : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m *
            aEtaZeroDvdPPow hp D.hζ D.equation D.hy) *
          (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m *
            (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
              (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) =
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) *
          (aEtaZeroDvdPPow hp D.hζ D.equation D.hy *
            (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
              (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) := by
      rw [show 2 * m = m + m by omega, pow_add]
      ring
    change rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (zetaSubOneDvdRoot hp D.hζ D.equation D.hy) *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero) = _
    rw [← h_first, ← h_sigma, hLHS_eq]
  have h_combined : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) *
        caseII_anchor_pair_div_p_pow_two_m D hp =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) *
        (aEtaZeroDvdPPow hp D.hζ D.equation D.hy *
          (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
            (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) := by
    rw [← h_spec, h_via_product]
  have h_p_ne_bot :
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥ := p_ne_zero D.hζ
  have h_p_pow_ne_bot :
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m)) ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot] at h_p_ne_bot ⊢
    exact pow_ne_zero _ h_p_ne_bot
  exact mul_left_cancel₀ h_p_pow_ne_bot h_combined

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`ringOfIntegersComplexConj` is involutive on `𝓞 K`.** Pointwise consequence of
`complexConj_apply_apply` on `K`, transferred to `𝓞 K` via `coe_ringOfIntegersComplexConj`. -/
theorem caseII_ringOfIntegersComplexConj_apply_self (x : 𝓞 K) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (NumberField.IsCMField.ringOfIntegersComplexConj K x) = x := by
  apply Subtype.ext
  change (NumberField.IsCMField.ringOfIntegersComplexConj K
    (NumberField.IsCMField.ringOfIntegersComplexConj K x) : K) = (x : K)
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    NumberField.IsCMField.complexConj_apply_apply]

/-- **σ-conjugate of `not_p_div_a_zero`: `𝔭 ∤ σ(𝔞₀)`.** Applying σ to `𝔭 ∣ σ(𝔞₀)` gives
`σ(𝔭) ∣ σ(σ(𝔞₀)) = 𝔞₀`. Since σ(𝔭) = 𝔭 and the involution gives `σ(σ(𝔞₀)) = 𝔞₀`, this
contradicts `not_p_div_a_zero`. -/
theorem caseII_not_p_div_a_etaInv_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  intro h
  have h_orig : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy :=
    not_p_div_a_zero hp D.hζ D.equation D.hy D.hz
  apply h_orig
  have h_le := Ideal.dvd_iff_le.mp h
  have h_le_mapped := Ideal.map_mono (f :=
    (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) h_le
  have h_invol_comp :
      ((NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom.comp
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) =
      RingHom.id (𝓞 K) := by
    apply RingHom.ext
    intro x
    exact caseII_ringOfIntegersComplexConj_apply_self x
  have h_invol_eq : ((aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy := by
    rw [Ideal.map_map]
    rw [show (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom.comp
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      RingHom.id (𝓞 K) from h_invol_comp]
    exact Ideal.map_id _
  have h_p_fixed : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.span_singleton_eq_span_singleton.mpr
      (caseII_sigma_zeta_sub_one_associated D).symm
  rw [h_invol_eq, h_p_fixed] at h_le_mapped
  exact Ideal.dvd_iff_le.mpr h_le_mapped

/-- **`𝔭 ∤ Q`** where `Q := pair / 𝔭^(2m)`. From `Q = 𝔞₀ · σ(𝔞₀)` (Q identification) and `𝔭` prime
(Dedekind / number-field), `𝔭 ∣ Q` would give `𝔭 ∣ 𝔞₀` or `𝔭 ∣ σ(𝔞₀)`, contradicting
`not_p_div_a_zero` / `caseII_not_p_div_a_etaInv_zero`. Foundation for the unramified-support
descent of Q to `𝓞 K⁺`. -/
theorem caseII_not_p_div_anchor_pair_div_p_pow_two_m {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      caseII_anchor_pair_div_p_pow_two_m D hp := by
  rw [caseII_anchor_pair_div_p_pow_two_m_eq D hp]
  intro h
  have hp_prime : Prime (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) :=
    Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime'
  rcases hp_prime.dvd_mul.mp h with h1 | h1
  · exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz h1
  · exact caseII_not_p_div_a_etaInv_zero D hp h1

/-- **`IsCoprime Q (37)` in `𝓞 K`.** From `𝔭 ∤ Q` and `Ideal.span {37} = 𝔭^36`
(via `Associated 37 ((ζ-1)^36)`), no prime ideal contains both Q and `(37)`, so they're
coprime. K-level analog of `caseII_isCoprime_rootIdeal_mul_int37` for the 𝔭-coprime
quotient Q. -/
theorem caseII_isCoprime_anchor_pair_div_int37 {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    IsCoprime (caseII_anchor_pair_div_p_pow_two_m D hp)
      (Ideal.span ({(37 : 𝓞 K)} : Set (𝓞 K))) := by
  have hsp : Ideal.span ({(37 : 𝓞 K)} : Set (𝓞 K)) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (37 - 1) := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
    exact_mod_cast (associated_zeta_sub_one_pow_prime D.hζ).symm
  rw [hsp]
  refine IsCoprime.pow_right ?_
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hQ_le hP_le hP_prime
  have hp_prime : Prime (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) :=
    Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime'
  haveI : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))).IsPrime :=
    (Ideal.prime_iff_isPrime hp_prime.ne_zero).mp hp_prime
  have hp_max : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hp_prime.ne_zero
  have hP_eq : P = Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
    (hp_max.eq_of_le hP_prime.ne_top hP_le).symm
  exact caseII_not_p_div_anchor_pair_div_p_pow_two_m D hp
    (Ideal.dvd_iff_le.mpr (hP_eq ▸ hQ_le))

/-- **`IsCoprime Q.comap (37 : 𝓞 K⁺)`.** The K⁺-comap of Q is coprime to `(37)` via the
same trace-based descent argument as `caseII_isCoprime_comap_int37`: from
`IsCoprime Q (37)` in `𝓞 K`, write `1 = a + 37·d`; then `2 = (a + σa) + 37·(d + σd)` with
`a + σa, d + σd ∈ 𝓞 K⁺` (σ-fixed), so `2 ∈ Q.comap + (37)` in `𝓞 K⁺`. Bézout
`1 = (-18)·2 + 37` upgrades to coprime. Uses `caseII_anchor_pair_div_p_pow_two_m_sigma_fixed`
(σ-stability of Q) and `caseII_isCoprime_anchor_pair_div_int37`. -/
theorem caseII_isCoprime_anchor_pair_div_comap_int37 {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    IsCoprime ((caseII_anchor_pair_div_p_pow_two_m D hp).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)))
      (Ideal.span ({(37 : 𝓞 (NumberField.maximalRealSubfield K))} :
        Set (𝓞 (NumberField.maximalRealSubfield K)))) := by
  set σ := (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom with hσ
  set Q := caseII_anchor_pair_div_p_pow_two_m D hp with hQ
  have hQ_stable : Q.map σ = Q := caseII_anchor_pair_div_p_pow_two_m_sigma_fixed D hp
  have hinv : ∀ x : 𝓞 K, σ (σ x) = x := caseII_ringOfIntegersComplexConj_apply_self
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp
    ((Ideal.isCoprime_iff_sup_eq.mp (caseII_isCoprime_anchor_pair_div_int37 D hp)) ▸
      (Submodule.mem_top : (1 : 𝓞 K) ∈ (⊤ : Ideal (𝓞 K))))
  have haσ_Q : a + σ a ∈ Q := Q.add_mem ha (hQ_stable ▸ Ideal.mem_map_of_mem σ ha)
  have haσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K (a + σ a) = a + σ a := by
    have h : σ (a + σ a) = a + σ a := by rw [map_add, hinv]; ring
    exact h
  obtain ⟨aP, haP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) (a + σ a)).mp haσ_fix)
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
  have hdσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K (d + σ d) = d + σ d := by
    have h : σ (d + σ d) = d + σ d := by rw [map_add, hinv]; ring
    exact h
  obtain ⟨eP, heP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) (d + σ d)).mp hdσ_fix)
  have hσ37 : σ (37 : 𝓞 K) = 37 := map_ofNat σ 37
  have hσ1 : σ a + 37 * σ d = 1 := by
    have h := congrArg σ hac
    rwa [map_add, map_mul, hσ37, map_one] at h
  have h2 : (2 : 𝓞 (NumberField.maximalRealSubfield K)) = aP + 37 * eP := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    rw [map_add, map_mul, haP, heP]
    simp only [map_ofNat]
    linear_combination -hac - hσ1
  have haP_mem : aP ∈ Q.comap
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
    rwa [Ideal.mem_comap, haP]
  have hbez : (1 : 𝓞 (NumberField.maximalRealSubfield K)) =
      (-18) * aP + (-18 * eP + 1) * 37 := by linear_combination (-18) * h2
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, hbez]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ haP_mem))
    (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

/-- **`Q.comap` is `Gal(K/K⁺)`-fixed** (the descent condition for
`comap_map_eq_of_unramifiedAt_support`). For `σ = 1` trivial; for `σ = complexConj` it is
the σ-stability `caseII_anchor_pair_div_p_pow_two_m_sigma_fixed` transported through
`caseII_galRestrict_complexConj_eq`. -/
theorem caseII_anchor_pair_div_comap_fixed {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (σ : K ≃ₐ[NumberField.maximalRealSubfield K] K) :
    (caseII_anchor_pair_div_p_pow_two_m D hp).comap
      (galRestrict (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K
        (𝓞 K) σ) =
    caseII_anchor_pair_div_p_pow_two_m D hp := by
  rcases BernoulliRegular.algEquiv_eq_one_or_complexConj (K := K) σ with h1 | hc
  · rw [h1, map_one]
    exact Ideal.comap_id _
  · rw [hc, caseII_galRestrict_complexConj_eq]
    nth_rewrite 1 [← caseII_anchor_pair_div_p_pow_two_m_sigma_fixed D hp]
    exact Ideal.comap_map_of_bijective _
      (EquivLike.bijective (NumberField.IsCMField.ringOfIntegersComplexConj K))

/-- **Q descends from `𝓞 K⁺`.** The `Gal(K/K⁺)`-fixed comap of Q satisfies `Q.comap.map = Q`,
applying `comap_map_eq_of_unramifiedAt_support` with the unramified-support condition
holding because every prime factor of `Q.comap` avoids the prime over 37 (else, with
`IsCoprime Q.comap (37)`, it would be `⊤`). -/
theorem caseII_anchor_pair_div_descends {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    ((caseII_anchor_pair_div_p_pow_two_m D hp).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).map
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      caseII_anchor_pair_div_p_pow_two_m D hp := by
  apply comap_map_eq_of_unramifiedAt_support (R := 𝓞 (NumberField.maximalRealSubfield K))
    (K := NumberField.maximalRealSubfield K) (L := K) (S := 𝓞 K)
  · exact caseII_anchor_pair_div_comap_fixed D hp
  · intro p hp_mem
    rw [Multiset.mem_toFinset] at hp_mem
    have hp_prime : Prime p := UniqueFactorizationMonoid.prime_of_factor p hp_mem
    haveI hp_isPrime : p.IsPrime := Ideal.isPrime_of_prime hp_prime
    apply isUnramifiedAt_of_not_over_37 p hp_prime.ne_zero
    intro h37
    have hcop := caseII_isCoprime_anchor_pair_div_comap_int37 D hp
    rw [Ideal.isCoprime_iff_sup_eq] at hcop
    have htop : (⊤ : Ideal (𝓞 (NumberField.maximalRealSubfield K))) ≤ p := by
      rw [← hcop]
      refine sup_le (Ideal.dvd_iff_le.mp (UniqueFactorizationMonoid.dvd_of_mem_factors hp_mem)) ?_
      rw [Ideal.span_singleton_le_iff_mem]
      have : (37 : 𝓞 (NumberField.maximalRealSubfield K)) =
          algebraMap ℤ (𝓞 (NumberField.maximalRealSubfield K)) 37 :=
        (map_ofNat (algebraMap ℤ (𝓞 (NumberField.maximalRealSubfield K))) 37).symm
      rwa [this]
    exact hp_isPrime.ne_top (top_le_iff.mp htop)

/-- **The σ-stable anchor descent J₀ exists.** For the anchor pair `(D.etaZero, η₀⁻¹)`,
there exists a K⁺-ideal `J₀ ≠ ⊥` whose extension to K equals the anchor pair product
`𝔞(η₀)·𝔞(η₀⁻¹)`. Construction: `J₀ := (span Λ)^m · Q.comap`, where
`Λ = (1-ζ)·(1-ζ^36)` is the K⁺-uniformizer at the prime over 37 and `Q` is the
𝔭-coprime quotient `pair / 𝔭^(2m)`. The extension to K is then
`(𝔭²)^m · Q = 𝔭^(2m) · Q = pair`. -/
theorem caseII_sigma_stable_anchor_pair_descent_exists {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    ∃ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
      J₀ ≠ ⊥ ∧
      J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
            (caseII_etaInv D.etaZero) := by
  refine ⟨(Ideal.span ({caseII_LambdaCyc D} :
    Set (𝓞 (NumberField.maximalRealSubfield K)))) ^ m *
      (caseII_anchor_pair_div_p_pow_two_m D hp).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)), ?_, ?_⟩
  · -- J₀ ≠ ⊥: both factors are nonzero.
    intro h
    rcases Ideal.mul_eq_bot.mp h with h | h
    · -- (span Λ)^m = ⊥ would give Λ = 0, but Λ ≠ 0.
      have h_Λ_ne_bot : Ideal.span ({caseII_LambdaCyc D} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact caseII_LambdaCyc_ne_zero D
      have h_pow_ne_bot : (Ideal.span ({caseII_LambdaCyc D} :
          Set (𝓞 (NumberField.maximalRealSubfield K)))) ^ m ≠ ⊥ := by
        rw [Ne, ← Ideal.zero_eq_bot] at h_Λ_ne_bot ⊢
        exact pow_ne_zero _ h_Λ_ne_bot
      exact h_pow_ne_bot h
    · -- Q.comap = ⊥ would give Q.comap.map = ⊥, but Q.comap.map = Q ≠ ⊥.
      have h_descent := caseII_anchor_pair_div_descends D hp
      rw [h, Ideal.map_bot] at h_descent
      exact caseII_anchor_pair_div_p_pow_two_m_ne_bot D hp h_descent.symm
  · -- J₀.map = 𝔭^(2m) · Q = pair (the defining spec)
    rw [Ideal.map_mul, caseII_LambdaCyc_pow_span_map_eq_zetaSubOne_pow_span,
      caseII_anchor_pair_div_descends D hp, ← Ideal.span_singleton_pow]
    exact (caseII_anchor_pair_div_p_pow_two_m_spec D hp).symm

/-- **The σ-stable anchored real-generator existence, unconditional.** Composes
`caseII_sigma_stable_anchor_pair_descent_exists` (which produces J₀ for the anchor pair)
with `caseII_sigma_stable_anchored_real_generator_exists` (which consumes J₀). Discharges
the anchor descent as a parametric input. From `RealCaseIIData37 D` and the K⁺-VC hypothesis
`h_VC`, produces real `x, y ∈ 𝓞 K⁺` (nonzero) with the σ-stable cross identity at any
σ-stable test pair `(η, caseII_etaInv η)`. This is the satisfiable replacement target
for the unsatisfiable raw quotient `𝔞(η)/𝔞₀`, fully constructed without taking the anchor
descent as an explicit hypothesis. -/
theorem caseII_sigma_stable_anchored_real_generator_unconditional {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero) :
    ∃ (x y : 𝓞 (NumberField.maximalRealSubfield K)), x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x} *
          (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) =
        Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y} *
          (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
              (caseII_etaInv D.etaZero)) := by
  obtain ⟨J₀, hJ0_ne, hJ0⟩ := caseII_sigma_stable_anchor_pair_descent_exists D hp
  exact caseII_sigma_stable_anchored_real_generator_exists D hp h_VC η hη hηinv hJ0_ne hJ0

/-- **Unconditional constructor for `CaseIISigmaPairAnchoredFixedGenerator37`.** Direct from
`RealCaseIIData37 D` + `h_VC`, without requiring the anchor descent as input — the anchor
descent J₀ is discharged internally by `caseII_sigma_stable_anchor_pair_descent_exists`. -/
noncomputable def caseII_sigma_pair_anchored_fixedGenerator_of_realData {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero) :
    CaseIISigmaPairAnchoredFixedGenerator37 D hp η := by
  have H := caseII_sigma_stable_anchored_real_generator_unconditional D hp h_VC η hη hηinv
  exact
    { xPlus := H.choose
      yPlus := H.choose_spec.choose
      xPlus_ne_zero := H.choose_spec.choose_spec.1
      yPlus_ne_zero := H.choose_spec.choose_spec.2.1
      cross_eq := H.choose_spec.choose_spec.2.2 }

/-- **Unconditional constructor for the adjacent σ-stable pair-generator record.** Direct
from `RealCaseIIData37 D` + `h_VC`, without requiring the anchor descent as input. Calls
`caseII_sigma_pair_anchored_fixedGenerator_of_realData` twice at D.etaOne and D.etaTwo. -/
noncomputable def caseII_sigma_pair_anchored_adjacent_of_realData {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (hη1inv : caseII_etaInv D.etaOne ≠ D.etaZero)
    (hη2inv : caseII_etaInv D.etaTwo ≠ D.etaZero) :
    CaseIISigmaPairAnchoredAdjacentFixedGenerators37 D hp where
  atEtaOne :=
    caseII_sigma_pair_anchored_fixedGenerator_of_realData D hp h_VC D.etaOne
      D.toCaseIIData37.etaOne_ne_etaZero hη1inv
  atEtaTwo :=
    caseII_sigma_pair_anchored_fixedGenerator_of_realData D hp h_VC D.etaTwo
      D.toCaseIIData37.etaTwo_ne_etaZero hη2inv

/-- **The σ-stable source for FLT37 Case-II II1, unconditional from K⁺-VC.** Given the
K⁺-class-group VC hypothesis (Sinnott's `37 ∤ h⁺`), the satisfiable σ-stable source
`CaseIISigmaPairAnchoredSource37` is constructible directly via the unconditional
adjacent constructor. This is the FLT37-endpoint-ready producer wired to the Sinnott
banked hypothesis. -/
noncomputable def caseII_sigma_pair_anchored_source_of_VC
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup
        (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))))) :
    CaseIISigmaPairAnchoredSource37 :=
  fun {_m} D hη1inv hη2inv =>
    caseII_sigma_pair_anchored_adjacent_of_realData D
      (by decide : (37 : ℕ) ≠ 2) h_VC hη1inv hη2inv

/-- **σ-stable cross identity (existential, K-level).** Existence form bundling the cross
identity for the σ-stable target η-pair under `RealCaseIIData37 + h_VC`. This is the
K-level statement of the producer's output, suitable for downstream consumption by a
σ-stable descent-step variant. -/
theorem caseII_sigma_pair_anchored_cross_identity_exists {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero) (hηinv : caseII_etaInv η ≠ D.etaZero) :
    ∃ (x y : 𝓞 (NumberField.maximalRealSubfield K)), x ≠ 0 ∧ y ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x)) *
          ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
              rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) :
            Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y)) *
          ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
              rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
                (caseII_etaInv D.etaZero) : Ideal (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K) := by
  let G := caseII_sigma_pair_anchored_fixedGenerator_of_realData D hp h_VC η hη hηinv
  refine ⟨G.xPlus, G.yPlus, G.xPlus_ne_zero, G.yPlus_ne_zero, ?_⟩
  exact caseII_sigma_pair_anchored_fractional_ratio D hp η G

set_option maxRecDepth 2000 in
/-- **`span{P_K_η} = (𝔪·𝔭)² · (𝔞_pair_η)^37`.** The K⁺-pair-generator's principal ideal
factors as the K-uniformizer/gcd part `(𝔪·𝔭)²` times the 37th power of the σ-stable
pair-product `𝔞_pair_η = 𝔞(η)·𝔞(η⁻¹)`. Combines `caseII_data_pair_realGenerator_K_principal_eq`
with `root_div_zeta_sub_one_dvd_gcd_spec` (`𝔠_η = 𝔞_η^37`). -/
theorem caseII_pair_realGenerator_K_eq_mp_pow_apair_pow {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    Ideal.span ({caseII_data_pair_realGenerator_K D η} : Set (𝓞 K)) =
      (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ 2 *
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 := by
  rw [caseII_data_pair_realGenerator_K_principal_eq D hp η]
  have h_𝔠η : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η =
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η) ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η).symm
  have h_𝔠ηinv : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) =
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)).symm
  rw [h_𝔠η, h_𝔠ηinv]
  rw [show (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 =
    (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η) ^ 37 *
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 from
    mul_pow _ _ _]
  set 𝔪 := gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))
  set 𝔭 := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))
  set A := (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η) ^ 37
  set B := (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37
  rw [show (𝔪 * A * 𝔭) * (𝔪 * B * 𝔭) = (𝔪 * 𝔭) * (𝔪 * 𝔭) * (A * B) by ring,
    show (𝔪 * 𝔭) * (𝔪 * 𝔭) = (𝔪 * 𝔭) ^ 2 by rw [sq]]

/-- **37th-power cross identity on K⁺-pair-generators.** From the σ-stable cross identity
`(x_i)·𝔞_pair_η_i = (y_i)·𝔞_pair_η_0` (cross_eq in `CaseIISigmaPairAnchoredFixedGenerator37`),
combined with `caseII_pair_realGenerator_K_eq_mp_pow_apair_pow`
(`span{P_K_η} = (𝔪·𝔭)²·(𝔞_pair_η)^37`), we have:
`(span x_K)^37 · span{P_K_η} = (𝔪·𝔭)² · ((x_K)·𝔞_pair_η)^37 = (𝔪·𝔭)² · ((y_K)·𝔞_pair_η_0)^37 =
(span y_K)^37 · span{P_K_η_0}`. This is the principal-ideal-level 37th-power identity that
feeds the Washington 9.4 descent equation. -/
theorem caseII_sigma_pair_pow37_cross_realGenerator {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus} :
        Set (𝓞 K)) ^ 37 *
        Ideal.span ({caseII_data_pair_realGenerator_K D η} : Set (𝓞 K)) =
      Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus} :
          Set (𝓞 K)) ^ 37 *
        Ideal.span ({caseII_data_pair_realGenerator_K D D.etaZero} : Set (𝓞 K)) := by
  rw [caseII_pair_realGenerator_K_eq_mp_pow_apair_pow D hp η,
    caseII_pair_realGenerator_K_eq_mp_pow_apair_pow D hp D.etaZero]
  set 𝔪𝔭2 := (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ 2
  set xK := Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus} :
    Set (𝓞 K))
  set yK := Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus} :
    Set (𝓞 K))
  set Aη := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)
  set Aη0 := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)
  rw [show xK ^ 37 * (𝔪𝔭2 * Aη ^ 37) = 𝔪𝔭2 * (xK * Aη) ^ 37 by rw [mul_pow]; ring,
    show yK ^ 37 * (𝔪𝔭2 * Aη0 ^ 37) = 𝔪𝔭2 * (yK * Aη0) ^ 37 by rw [mul_pow]; ring]
  rw [G.cross_eq]

/-- **Element-level 37th-power Associated identity.** Two principal ideals in `𝓞 K` are
equal iff their generators are Associated. Combined with the 37th-power cross identity, this
gives `Associated ((algebraMap x_K)^37 · P_K_η) ((algebraMap y_K)^37 · P_K_η₀)` — a
direct element-level identity (up to unit) that is the immediate input to the Washington
9.4 descent equation. -/
theorem caseII_sigma_pair_pow37_cross_realGenerator_associated {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    Associated
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D η)
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D D.etaZero) := by
  have h := caseII_sigma_pair_pow37_cross_realGenerator D hp η G
  have h_LHS : Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus} :
        Set (𝓞 K)) ^ 37 *
        Ideal.span ({caseII_data_pair_realGenerator_K D η} : Set (𝓞 K)) =
      Ideal.span ({(algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D η} : Set (𝓞 K)) := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  have h_RHS : Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus} :
        Set (𝓞 K)) ^ 37 *
        Ideal.span ({caseII_data_pair_realGenerator_K D D.etaZero} : Set (𝓞 K)) =
      Ideal.span ({(algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D D.etaZero} : Set (𝓞 K)) := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [h_LHS, h_RHS] at h
  exact Ideal.span_singleton_eq_span_singleton.mp h

/-- **Element-level 37th-power cross identity with explicit unit.** From the Associated
form, extract a unit `u ∈ (𝓞 K)ˣ` realising the cross relation:
`(x_K)^37 · P_K_η · u = (y_K)^37 · P_K_η₀`. This is the explicit element-level identity
consumed by the Washington 9.4 descent derivation: substituting `P_K = (x'+y'·η)(x'+y'·η⁻¹)`
gives the polynomial relation among `x', y', η_i, η_0` that becomes the descent equation. -/
theorem caseII_sigma_pair_pow37_cross_realGenerator_unit {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u : (𝓞 K)ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D η * u =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D D.etaZero := by
  have h := caseII_sigma_pair_pow37_cross_realGenerator_associated D hp η G
  obtain ⟨u, hu⟩ := h
  exact ⟨u, hu⟩

/-- **σ-fixedness of the cross-unit u.** The unit `u` from
`caseII_sigma_pair_pow37_cross_realGenerator_unit` satisfies `σ(u) = u`. Both sides of the
defining identity `(x_K)^37·P_K_η·u = (y_K)^37·P_K_η₀` are σ-fixed (x_K, y_K, P_K all come
from `𝓞 K⁺`), so cancellation gives σ-fixedness of u. -/
theorem caseII_sigma_pair_pow37_cross_realGenerator_unit_fixed {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η)
    (u : (𝓞 K)ˣ)
    (hu : (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D η * (u : 𝓞 K) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D D.etaZero) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) = (u : 𝓞 K) := by
  set σ : 𝓞 K →+* 𝓞 K :=
    (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom
  have h_x_fixed_atom :
      σ (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus :=
    ringOfIntegersComplexConj_algebraMap_eq (K := K) G.xPlus
  have h_y_fixed_atom :
      σ (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus :=
    ringOfIntegersComplexConj_algebraMap_eq (K := K) G.yPlus
  have h_x_fixed : σ ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 := by
    rw [map_pow, h_x_fixed_atom]
  have h_y_fixed : σ ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 := by
    rw [map_pow, h_y_fixed_atom]
  have h_P_fixed : σ (caseII_data_pair_realGenerator_K D η) =
      caseII_data_pair_realGenerator_K D η :=
    caseII_data_pair_realGenerator_K_real D η
  have h_P0_fixed : σ (caseII_data_pair_realGenerator_K D D.etaZero) =
      caseII_data_pair_realGenerator_K D D.etaZero :=
    caseII_data_pair_realGenerator_K_real D D.etaZero
  have h_σ := congrArg σ hu
  simp only [map_mul] at h_σ
  rw [h_x_fixed, h_P_fixed, h_y_fixed, h_P0_fixed] at h_σ
  rw [← hu] at h_σ
  have h_P_K_ne_zero : caseII_data_pair_realGenerator_K D η ≠ 0 := by
    unfold caseII_data_pair_realGenerator_K
    rw [Ne, map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))]
    exact caseII_data_pair_realGenerator_ne_zero D hp η
  have h_x_ne_zero : (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
      caseII_data_pair_realGenerator_K D η ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by
        rw [Ne, map_eq_zero_iff _
          (FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))]
        exact G.xPlus_ne_zero)
    · exact h_P_K_ne_zero
  have h_eq : σ (u : 𝓞 K) = (u : 𝓞 K) := mul_left_cancel₀ h_x_ne_zero h_σ
  exact h_eq

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **σ-fixed unit descends to `𝓞 K⁺`.** Bundles the σ-fixedness of u with the
`ringOfIntegersComplexConj_eq_self_iff` characterisation to give a preimage in
`𝓞 K⁺` mapping back to u. -/
theorem caseII_sigma_unit_descends_K_plus {u : 𝓞 K}
    (hu : NumberField.IsCMField.ringOfIntegersComplexConj K u = u) :
    ∃ u' : 𝓞 (NumberField.maximalRealSubfield K),
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) u' = u :=
  (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) u).mp hu

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **σ-fixed K-unit lifts to a K⁺-unit.** Given a unit `u ∈ (𝓞 K)ˣ` with `σ(u) = u`,
there exists a K⁺-unit `u' ∈ (𝓞 K⁺)ˣ` with `algebraMap u' = u`. The K⁺-inverse of `u'`
comes from `u⁻¹` (also σ-fixed since `u` is). -/
theorem caseII_sigma_K_unit_lifts_K_plus_unit (u : (𝓞 K)ˣ)
    (hu : NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) = (u : 𝓞 K)) :
    ∃ u' : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u' : 𝓞 _) = (u : 𝓞 K) := by
  obtain ⟨a, ha⟩ := caseII_sigma_unit_descends_K_plus hu
  have hu_inv : NumberField.IsCMField.ringOfIntegersComplexConj K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) =
      ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    have h1 : (u : 𝓞 K) *
        (NumberField.IsCMField.ringOfIntegersComplexConj K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) = 1 := by
      have h_sigma_id := congrArg
        (NumberField.IsCMField.ringOfIntegersComplexConj K)
        (show (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      rwa [map_mul, hu, map_one] at h_sigma_id
    have h2 : (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h_u_unit : IsUnit (u : 𝓞 K) := u.isUnit
    exact h_u_unit.mul_left_cancel (h1.trans h2.symm)
  obtain ⟨b, hb⟩ := caseII_sigma_unit_descends_K_plus hu_inv
  have h_ab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    rw [map_mul, ha, hb, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨⟨a, b, h_ab, ?_⟩, ?_⟩
  · rwa [mul_comm]
  · exact ha

/-- **K⁺-level element identity from σ-stable cross + σ-fixed cross-unit.** Combining
`caseII_sigma_pair_pow37_cross_realGenerator_unit` +
`caseII_sigma_pair_pow37_cross_realGenerator_unit_fixed`
+ `caseII_sigma_K_unit_lifts_K_plus_unit`: there exist real K⁺-pair-generators
`(P_K⁺_η, P_K⁺_η₀)` and a real K⁺-unit `u_K⁺ ∈ (𝓞 K⁺)ˣ` realising the K⁺-level
element identity `(x_K⁺)^37 · P_K⁺_η · u_K⁺ = (y_K⁺)^37 · P_K⁺_η₀`. This is the
direct input to the descent equation derivation. -/
theorem caseII_sigma_pair_pow37_K_plus_identity {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      G.xPlus ^ 37 * caseII_data_pair_realGenerator D η * (u_KP : 𝓞 _) =
      G.yPlus ^ 37 * caseII_data_pair_realGenerator D D.etaZero := by
  obtain ⟨u, hu⟩ := caseII_sigma_pair_pow37_cross_realGenerator_unit D hp η G
  have hu_fixed := caseII_sigma_pair_pow37_cross_realGenerator_unit_fixed D hp η G u hu
  obtain ⟨u_KP, hu_KP⟩ := caseII_sigma_K_unit_lifts_K_plus_unit u hu_fixed
  refine ⟨u_KP, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  simp only [map_mul, map_pow]
  have h_P_η : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_data_pair_realGenerator D η) = caseII_data_pair_realGenerator_K D η := rfl
  have h_P_η0 : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_data_pair_realGenerator D D.etaZero) =
      caseII_data_pair_realGenerator_K D D.etaZero := rfl
  rw [h_P_η, h_P_η0, hu_KP]
  exact hu

/-- **Two-root ratio K⁺-level identity: eliminating P_K⁺_η_0.** From two σ-stable generator
records `G_1` at `η_1` and `G_2` at `η_2`, the K⁺-level 37th-power cross identity at each
combined to eliminate P_K⁺_η_0 gives:
`((y_2·x_1))^37 · P_K⁺_η_1 · u_1 = ((y_1·x_2))^37 · P_K⁺_η_2 · u_2`.
This is the two-root form used in the Diekmann ratio descent. -/
theorem caseII_sigma_pair_pow37_K_plus_two_root_identity {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp η₁)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp η₂) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (G₂.yPlus * G₁.xPlus) ^ 37 * caseII_data_pair_realGenerator D η₁ * (u₁ : 𝓞 _) =
      (G₁.yPlus * G₂.xPlus) ^ 37 * caseII_data_pair_realGenerator D η₂ * (u₂ : 𝓞 _) := by
  obtain ⟨u₁, h₁⟩ := caseII_sigma_pair_pow37_K_plus_identity D hp η₁ G₁
  obtain ⟨u₂, h₂⟩ := caseII_sigma_pair_pow37_K_plus_identity D hp η₂ G₂
  refine ⟨u₁, u₂, ?_⟩
  have h_mul_1 : ↑G₂.yPlus ^ 37 *
      (↑G₁.xPlus ^ 37 * caseII_data_pair_realGenerator D η₁ * (u₁ : 𝓞 _)) =
      ↑G₂.yPlus ^ 37 * (↑G₁.yPlus ^ 37 * caseII_data_pair_realGenerator D D.etaZero) := by
    rw [h₁]
  have h_mul_2 : ↑G₁.yPlus ^ 37 *
      (↑G₂.xPlus ^ 37 * caseII_data_pair_realGenerator D η₂ * (u₂ : 𝓞 _)) =
      ↑G₁.yPlus ^ 37 * (↑G₂.yPlus ^ 37 * caseII_data_pair_realGenerator D D.etaZero) := by
    rw [h₂]
  have h_eq_RHS : ↑G₂.yPlus ^ 37 *
        (↑G₁.yPlus ^ 37 * caseII_data_pair_realGenerator D D.etaZero) =
      ↑G₁.yPlus ^ 37 *
        (↑G₂.yPlus ^ 37 * caseII_data_pair_realGenerator D D.etaZero) := by ring
  have h_LHS_eq : ↑G₂.yPlus ^ 37 *
        (↑G₁.xPlus ^ 37 * caseII_data_pair_realGenerator D η₁ * (u₁ : 𝓞 _)) =
      ↑G₁.yPlus ^ 37 *
        (↑G₂.xPlus ^ 37 * caseII_data_pair_realGenerator D η₂ * (u₂ : 𝓞 _)) := by
    rw [h_mul_1, h_eq_RHS, h_mul_2]
  have h_target : ↑G₂.yPlus ^ 37 *
        (↑G₁.xPlus ^ 37 * caseII_data_pair_realGenerator D η₁ * (u₁ : 𝓞 _)) =
      (G₂.yPlus * G₁.xPlus) ^ 37 * caseII_data_pair_realGenerator D η₁ * (u₁ : 𝓞 _) := by
    rw [mul_pow]
    ring
  have h_target_2 : ↑G₁.yPlus ^ 37 *
        (↑G₂.xPlus ^ 37 * caseII_data_pair_realGenerator D η₂ * (u₂ : 𝓞 _)) =
      (G₁.yPlus * G₂.xPlus) ^ 37 * caseII_data_pair_realGenerator D η₂ * (u₂ : 𝓞 _) := by
    rw [mul_pow]
    ring
  rw [← h_target, ← h_target_2]
  exact h_LHS_eq

/-- **Two-root identity expanded via the polynomial form.** Substituting
`P_K⁺_η = xP² + xP·yP·γ_η + yP²` (from `caseII_data_pair_realGenerator_eq_polynomial`)
into the two-root cross identity gives an explicit polynomial form:
`(y_2·x_1)^37 · (xP² + xP·yP·γ_1 + yP²) · u_1 = (y_1·x_2)^37 · (xP² + xP·yP·γ_2 + yP²) · u_2`.
This is the polynomial expansion fed into the Diekmann descent equation extraction. -/
theorem caseII_sigma_pair_pow37_K_plus_two_root_polynomial {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp η₁)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp η₂) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (G₂.yPlus * G₁.xPlus) ^ 37 *
        (caseII_data_xP D ^ 2 +
          caseII_data_xP D * caseII_data_yP D *
            caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₁.2) +
          caseII_data_yP D ^ 2) *
        (u₁ : 𝓞 _) =
      (G₁.yPlus * G₂.xPlus) ^ 37 *
        (caseII_data_xP D ^ 2 +
          caseII_data_xP D * caseII_data_yP D *
            caseII_eta_trace ((mem_nthRootsFinset (by norm_num) _).mp η₂.2) +
          caseII_data_yP D ^ 2) *
        (u₂ : 𝓞 _) := by
  obtain ⟨u₁, u₂, h⟩ := caseII_sigma_pair_pow37_K_plus_two_root_identity D hp η₁ η₂ G₁ G₂
  refine ⟨u₁, u₂, ?_⟩
  rw [← caseII_data_pair_realGenerator_eq_polynomial,
    ← caseII_data_pair_realGenerator_eq_polynomial]
  exact h

/-- **The (x_KP)^37 · P_K⁺_η factor is nonzero in `𝓞 K⁺`.** Both `x_KP ≠ 0` and the
K⁺-pair-realGenerator is nonzero (from `caseII_data_pair_realGenerator_ne_zero`). -/
theorem caseII_sigma_pair_pow37_lhs_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    G.xPlus ^ 37 * caseII_data_pair_realGenerator D η ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ G.xPlus_ne_zero)
    (caseII_data_pair_realGenerator_ne_zero D hp η)

/-- **K-level lift of the two-root identity.** Applying `algebraMap` to both sides of the
K⁺-level two-root identity gives the K-level analog with `D.x, D.y` instead of `xP, yP`:
`(algebraMap (y_2·x_1))^37 · (D.x + D.y·η_1)·(D.x + D.y·η_1^36) · algebraMap u_1 =
(algebraMap (y_1·x_2))^37 · (D.x + D.y·η_2)·(D.x + D.y·η_2^36) · algebraMap u_2`. -/
theorem caseII_sigma_pair_pow37_K_two_root_identity {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp η₁)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp η₂) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₂.yPlus * G₁.xPlus)) ^ 37 *
        ((D.x + D.y * (η₁ : 𝓞 K)) * (D.x + D.y * (η₁ : 𝓞 K) ^ 36)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₁.yPlus * G₂.xPlus)) ^ 37 *
        ((D.x + D.y * (η₂ : 𝓞 K)) * (D.x + D.y * (η₂ : 𝓞 K) ^ 36)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) := by
  obtain ⟨u₁, u₂, h⟩ := caseII_sigma_pair_pow37_K_plus_two_root_identity D hp η₁ η₂ G₁ G₂
  refine ⟨u₁, u₂, ?_⟩
  have h_K := congrArg (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) h
  simp only [map_mul, map_pow] at h_K
  rw [show (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
      (caseII_data_pair_realGenerator D η₁) =
      (D.x + D.y * (η₁ : 𝓞 K)) * (D.x + D.y * (η₁ : 𝓞 K) ^ 36) from
    caseII_data_pair_realGenerator_K_eq D η₁] at h_K
  rw [show (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
      (caseII_data_pair_realGenerator D η₂) =
      (D.x + D.y * (η₂ : 𝓞 K)) * (D.x + D.y * (η₂ : 𝓞 K) ^ 36) from
    caseII_data_pair_realGenerator_K_eq D η₂] at h_K
  exact h_K

/-- **K-level two-root identity with adjacent Case-II roots.** Specialisation of
`caseII_sigma_pair_pow37_K_two_root_identity` to `η_1 = D.etaOne`, `η_2 = D.etaTwo` (the
adjacent roots `η₀·ζ` and `η₀·ζ²`). This is the K-level form at the Case-II adjacent test
pair, immediate input to the Diekmann descent. -/
theorem caseII_sigma_pair_pow37_K_adjacent_identity {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₂.yPlus * G₁.xPlus)) ^ 37 *
        ((D.x + D.y * (D.etaOne : 𝓞 K)) * (D.x + D.y * (D.etaOne : 𝓞 K) ^ 36)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₁.yPlus * G₂.xPlus)) ^ 37 *
        ((D.x + D.y * (D.etaTwo : 𝓞 K)) * (D.x + D.y * (D.etaTwo : 𝓞 K) ^ 36)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) :=
  caseII_sigma_pair_pow37_K_two_root_identity D hp D.etaOne D.etaTwo G₁ G₂

/-- **Unconditional K-level adjacent identity.** Provided only `RealCaseIIData37 D` + `h_VC`
(Sinnott's `37 ∤ h⁺`), there exist real K⁺-data `(x_1, y_1, x_2, y_2, u_1, u_2)` realising
the K-level adjacent two-root cross identity. The G₁, G₂ from
`caseII_sigma_pair_anchored_fixedGenerator_of_realData` provide the K⁺-preimages internally;
this packages the resulting K-level identity as an existence statement. -/
theorem caseII_sigma_pair_pow37_K_adjacent_identity_unconditional {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (hη1inv : caseII_etaInv D.etaOne ≠ D.etaZero)
    (hη2inv : caseII_etaInv D.etaTwo ≠ D.etaZero) :
    ∃ (x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K))
      (u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      x₁ ≠ 0 ∧ y₁ ≠ 0 ∧ x₂ ≠ 0 ∧ y₂ ≠ 0 ∧
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (y₂ * x₁)) ^ 37 *
          ((D.x + D.y * (D.etaOne : 𝓞 K)) * (D.x + D.y * (D.etaOne : 𝓞 K) ^ 36)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) =
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (y₁ * x₂)) ^ 37 *
          ((D.x + D.y * (D.etaTwo : 𝓞 K)) * (D.x + D.y * (D.etaTwo : 𝓞 K) ^ 36)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) := by
  let G₁ := caseII_sigma_pair_anchored_fixedGenerator_of_realData D hp h_VC D.etaOne
    D.toCaseIIData37.etaOne_ne_etaZero hη1inv
  let G₂ := caseII_sigma_pair_anchored_fixedGenerator_of_realData D hp h_VC D.etaTwo
    D.toCaseIIData37.etaTwo_ne_etaZero hη2inv
  obtain ⟨u₁, u₂, h⟩ := caseII_sigma_pair_pow37_K_adjacent_identity D hp G₁ G₂
  exact ⟨G₁.xPlus, G₁.yPlus, G₂.xPlus, G₂.yPlus, u₁, u₂,
    G₁.xPlus_ne_zero, G₁.yPlus_ne_zero, G₂.xPlus_ne_zero, G₂.yPlus_ne_zero, h⟩

/-- **K-level pair-product symmetric expansion.** For `η : nthRootsFinset 37 (1 : 𝓞 K)`:
`(D.x + D.y·η)·(D.x + D.y·η^36) = D.x² + D.x·D.y·(η + η^36) + D.y²`. Proof: expand,
use `η·η^36 = η^37 = 1`. -/
theorem caseII_pair_product_symmetric_expansion {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) =
      D.x ^ 2 + D.x * D.y * ((η : 𝓞 K) + (η : 𝓞 K) ^ 36) + D.y ^ 2 := by
  have hη : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have h_eta_prod : (η : 𝓞 K) * (η : 𝓞 K) ^ 36 = 1 := by
    rw [← pow_succ']
    exact hη
  ring_nf
  rw [show (η : 𝓞 K) ^ 37 = (η : 𝓞 K) * (η : 𝓞 K) ^ 36 by rw [← pow_succ'], h_eta_prod]
  ring

/-- **K-level adjacent identity in symmetric polynomial form.** Substituting
the symmetric expansion `(D.x + D.y·η)·(D.x + D.y·η^36) = D.x² + D.x·D.y·(η + η^36) + D.y²`
into the K-level adjacent identity gives the polynomial form
`A^37 · (D.x² + D.x·D.y·γ_1 + D.y²) · u_1 = B^37 · (D.x² + D.x·D.y·γ_2 + D.y²) · u_2`
with `γ_i := η_i + η_i^36` (σ-fixed K-trace). This is the polynomial form that
the Diekmann descent extracts a 37th-power from. -/
theorem caseII_sigma_pair_pow37_K_adjacent_symmetric {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₂.yPlus * G₁.xPlus)) ^ 37 *
        (D.x ^ 2 + D.x * D.y * ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) + D.y ^ 2) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₁.yPlus * G₂.xPlus)) ^ 37 *
        (D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) := by
  obtain ⟨u₁, u₂, h⟩ := caseII_sigma_pair_pow37_K_adjacent_identity D hp G₁ G₂
  refine ⟨u₁, u₂, ?_⟩
  rw [← caseII_pair_product_symmetric_expansion D D.etaOne,
    ← caseII_pair_product_symmetric_expansion D D.etaTwo]
  exact h

/-- **K-level pair-product symmetric difference: D.x·D.y cross term.** The K-level analog
of `caseII_pair_diff_eq_cross_term`: subtracting two symmetric polynomial forms isolates
the bilinear D.x·D.y term:
`(D.x²+D.x·D.y·γ_1+D.y²) - (D.x²+D.x·D.y·γ_2+D.y²) = D.x·D.y·(γ_1 - γ_2)`.
Used in the Diekmann descent's Cramer-step isolation. -/
theorem caseII_K_pair_symmetric_diff {m : ℕ} (D : RealCaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.x ^ 2 + D.x * D.y * ((η₁ : 𝓞 K) + (η₁ : 𝓞 K) ^ 36) + D.y ^ 2) -
        (D.x ^ 2 + D.x * D.y * ((η₂ : 𝓞 K) + (η₂ : 𝓞 K) ^ 36) + D.y ^ 2) =
      D.x * D.y * (((η₁ : 𝓞 K) + (η₁ : 𝓞 K) ^ 36) -
        ((η₂ : 𝓞 K) + (η₂ : 𝓞 K) ^ 36)) := by ring

/-- **K-level Cramer-step: isolate D.x·D.y from the adjacent identity + symmetric difference.**
From the K-level adjacent identity `A^37·Q_1·u_1 = B^37·Q_2·u_2` and the symmetric
difference `Q_1 - Q_2 = D.x·D.y·(γ_1 - γ_2)`, we get the elimination form
`Q_2·(A^37·u_1 - B^37·u_2) = -A^37·u_1·D.x·D.y·(γ_1 - γ_2)`.
This isolates `(A^37·u_1 - B^37·u_2)` in terms of D.x·D.y times the K-trace difference,
the Cramer-step input to the Diekmann descent. -/
theorem caseII_K_pair_cramer_isolate_xy {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2) *
          ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
              (G₂.yPlus * G₁.xPlus)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) -
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
              (G₁.yPlus * G₂.xPlus)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _))) =
        -((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (G₂.yPlus * G₁.xPlus)) ^ 37 *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _))) *
          (D.x * D.y * (((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) -
            ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36))) := by
  obtain ⟨u₁, u₂, h⟩ := caseII_sigma_pair_pow37_K_adjacent_symmetric D hp G₁ G₂
  refine ⟨u₁, u₂, ?_⟩
  have h_diff := caseII_K_pair_symmetric_diff D D.etaOne D.etaTwo
  linear_combination h - h_diff *
    ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (G₂.yPlus * G₁.xPlus)) ^ 37 *
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)))

/-- **The K⁺-pair-generator at η_2 is nonzero.** Specialization of
`caseII_data_pair_realGenerator_K_real`-like reasoning: in 𝓞 K, the symmetric
polynomial `D.x² + D.x·D.y·γ_η₂ + D.y²` factors as `(D.x + D.y·η_2)·(D.x + D.y·η_2^36)`,
and both factors are nonzero (D.y ≠ 0 from hy, and a + b·η = 0 would force a/b = -η
which would contradict the Case-II descent hypotheses). -/
theorem caseII_K_symmetric_at_etaTwo_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2 ≠ 0 := by
  rw [← caseII_pair_product_symmetric_expansion D D.etaTwo,
    ← caseII_data_pair_realGenerator_K_eq D D.etaTwo]
  unfold caseII_data_pair_realGenerator_K
  rw [Ne, map_eq_zero_iff _
    (FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))]
  exact caseII_data_pair_realGenerator_ne_zero D hp D.etaTwo

/-- **The K-symmetric polynomial form at `D.etaOne` is nonzero.** Companion to
`caseII_K_symmetric_at_etaTwo_ne_zero`. -/
theorem caseII_K_symmetric_at_etaOne_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    D.x ^ 2 + D.x * D.y * ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) + D.y ^ 2 ≠ 0 := by
  rw [← caseII_pair_product_symmetric_expansion D D.etaOne,
    ← caseII_data_pair_realGenerator_K_eq D D.etaOne]
  unfold caseII_data_pair_realGenerator_K
  rw [Ne, map_eq_zero_iff _
    (FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))]
  exact caseII_data_pair_realGenerator_ne_zero D hp D.etaOne

/-- **Explicit coe of `D.etaOne` as `η₀ · ζ`.** Direct unfolding. -/
theorem caseII_etaOne_coe_eq {m : ℕ} (D : RealCaseIIData37 K m) :
    (D.etaOne : 𝓞 K) = (D.etaZero : 𝓞 K) * D.hζ.toInteger := by
  rfl

/-- **Explicit coe of `D.etaTwo` as `η₀ · ζ²`.** Direct unfolding. -/
theorem caseII_etaTwo_coe_eq {m : ℕ} (D : RealCaseIIData37 K m) :
    (D.etaTwo : 𝓞 K) = (D.etaZero : 𝓞 K) * D.hζ.toInteger * D.hζ.toInteger := by
  rfl

/-- **σ-anchor identity for RealCaseIIData37: `caseII_etaInv D.etaZero = D.etaZero`.** From
real-data σ-symmetry: `𝔭^m ∣ 𝔞(caseII_etaInv D.etaZero)` (caseII_p_pow_dvd_a_caseII_etaInv_etaZero)
combined with the iff `p_dvd_a_iff` (𝔭 ∣ 𝔞(η) ↔ η = D.etaZero) forces the σ-conjugate to
equal D.etaZero. Combined with `η^37 = 1`, this implies `(D.etaZero : 𝓞 K) = 1`
(the cube of η^36 = η forces η^35 = 1 = η^37; gcd(35,37)=1 implies η = 1). -/
theorem caseII_etaInv_etaZero_eq_etaZero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    caseII_etaInv D.etaZero = D.etaZero := by
  have h_dvd := caseII_p_pow_dvd_a_caseII_etaInv_etaZero D hp
  have hm : 1 ≤ m := D.toCaseIIData37.one_le_m
  have h_p_dvd : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (caseII_etaInv D.etaZero) := by
    have : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m :=
      dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp hm)
    exact dvd_trans this h_dvd
  have h_eq : caseII_etaInv D.etaZero =
      zetaSubOneDvdRoot hp D.hζ D.equation D.hy :=
    (p_dvd_a_iff hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)).mp h_p_dvd
  have h_anchor : (zetaSubOneDvdRoot hp D.hζ D.equation D.hy :
      nthRootsFinset 37 (1 : 𝓞 K)) = D.etaZero := by
    simp [CaseIIData37.etaZero]
  exact h_eq.trans h_anchor

/-- **In `RealCaseIIData37`, `(D.etaZero : 𝓞 K) = 1`.** From
`caseII_etaInv D.etaZero = D.etaZero` (i.e., `(D.etaZero)^36 = D.etaZero`), multiplying both
sides by `D.etaZero` gives `(D.etaZero)^37 = (D.etaZero)^2`, and `(D.etaZero)^37 = 1`, so
`(D.etaZero)^2 = 1`, hence `D.etaZero = ±1`. Since 37 is odd, `-1` is not a 37th root, so
`D.etaZero = 1`. -/
theorem caseII_etaZero_eq_one {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.etaZero : 𝓞 K) = 1 := by
  have h_etaInv_eq := caseII_etaInv_etaZero_eq_etaZero D hp
  have h_coe : (D.etaZero : 𝓞 K) ^ 36 = (D.etaZero : 𝓞 K) := by
    have h_subtype := congrArg (fun η : nthRootsFinset 37 (1 : 𝓞 K) => (η : 𝓞 K)) h_etaInv_eq
    rwa [caseII_etaInv_coe] at h_subtype
  have h37 : (D.etaZero : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp D.etaZero.2
  have h_sq : (D.etaZero : 𝓞 K) ^ 2 = 1 := by
    calc (D.etaZero : 𝓞 K) ^ 2
        = (D.etaZero : 𝓞 K) * (D.etaZero : 𝓞 K) := by ring
      _ = (D.etaZero : 𝓞 K) ^ 36 * (D.etaZero : 𝓞 K) := by rw [h_coe]
      _ = (D.etaZero : 𝓞 K) ^ 37 := by ring
      _ = 1 := h37
  have h_36 : (D.etaZero : 𝓞 K) ^ 36 = 1 := by
    calc (D.etaZero : 𝓞 K) ^ 36
        = ((D.etaZero : 𝓞 K) ^ 2) ^ 18 := by ring
      _ = 1 ^ 18 := by rw [h_sq]
      _ = 1 := one_pow _
  have h_split : (D.etaZero : 𝓞 K) ^ 37 = (D.etaZero : 𝓞 K) ^ 36 * (D.etaZero : 𝓞 K) := by
    rw [← pow_succ]
  rw [h_36, one_mul] at h_split
  exact h_split.symm.trans h37

/-- **The K-trace difference `γ_1 - γ_2` factors as `(ζ - 1) · (η₀^36·ζ^35 - η₀·ζ)`.**
With γ_1 = η_0·ζ + (η_0·ζ)^36 and γ_2 = η_0·ζ² + (η_0·ζ²)^36, expansion + ring give the
factorization. The (ζ - 1) factor is the K-uniformizer at 𝔭; the cofactor lies in the 𝔭-coprime
part. This is the structural fact underlying the Diekmann descent's 𝔭-uniformizer extraction. -/
theorem caseII_K_trace_diff_factors {m : ℕ} (D : RealCaseIIData37 K m)
    (_hp : (37 : ℕ) ≠ 2) :
    ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) -
        ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) =
      (D.hζ.toInteger - 1) *
        ((D.etaZero : 𝓞 K) ^ 36 * (D.hζ.toInteger : 𝓞 K) ^ 35 -
          (D.etaZero : 𝓞 K) * D.hζ.toInteger) := by
  rw [caseII_etaOne_coe_eq, caseII_etaTwo_coe_eq]
  set ζ : 𝓞 K := D.hζ.toInteger
  set η₀ : 𝓞 K := (D.etaZero : 𝓞 K)
  have hζ37 : ζ ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have h36 : (η₀ * ζ) ^ 36 = η₀ ^ 36 * ζ ^ 36 := by ring
  have h72_eq_35 : ζ ^ 72 = ζ ^ 35 := by
    have : ζ ^ 72 = ζ ^ 37 * ζ ^ 35 := by ring
    rw [this, hζ37, one_mul]
  have h36' : (η₀ * ζ * ζ) ^ 36 = η₀ ^ 36 * ζ ^ 35 := by
    rw [show η₀ * ζ * ζ = η₀ * ζ ^ 2 by ring, mul_pow, ← pow_mul,
      show (2 * 36 : ℕ) = 72 by norm_num, h72_eq_35]
  rw [h36, h36']
  ring

/-- **Simplified K-trace difference under `D.etaZero = 1`:** `γ_1 - γ_2 = (ζ - 1) · (ζ^35 - ζ)`.
Substituting `D.etaZero = 1` (from `caseII_etaZero_eq_one`) into
`caseII_K_trace_diff_factors` gives this simpler form. -/
theorem caseII_K_trace_diff_factors_simplified {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) -
        ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) =
      (D.hζ.toInteger - 1) *
        ((D.hζ.toInteger : 𝓞 K) ^ 35 - D.hζ.toInteger) := by
  have h_factors := caseII_K_trace_diff_factors D hp
  have h_etaZero_one := caseII_etaZero_eq_one D hp
  rw [h_factors, h_etaZero_one]
  ring

/-- **`Associated (ζ^k - 1) (ζ - 1)` for k coprime to 37.** From mathlib's
`IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`. -/
theorem caseII_zeta_pow_sub_one_associated {m : ℕ} (D : RealCaseIIData37 K m)
    (k : ℕ) (hk : k.Coprime 37) :
    Associated ((D.hζ.toInteger : 𝓞 K) ^ k - 1) (D.hζ.toInteger - 1) :=
  (D.hζ.toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime hk).symm

/-- **`(ζ - 1)² ∣ γ_1 - γ_2`.** From the factorization
`γ_1 - γ_2 = (ζ - 1)·ζ·(ζ^34 - 1)` and `Associated (ζ^34 - 1) (ζ - 1)`, the trace difference
has `(ζ - 1)²` as a divisor (via `dvd_mul_of_dvd_left` on the associated form). -/
theorem caseII_K_zeta_sub_one_sq_dvd_trace_diff {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣
      ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) -
        ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) := by
  rw [caseII_K_trace_diff_factors_simplified D hp]
  have h_factor : (D.hζ.toInteger : 𝓞 K) ^ 35 - D.hζ.toInteger =
      D.hζ.toInteger * ((D.hζ.toInteger : 𝓞 K) ^ 34 - 1) := by ring
  rw [h_factor]
  have h_assoc : Associated ((D.hζ.toInteger : 𝓞 K) ^ 34 - 1) (D.hζ.toInteger - 1) :=
    caseII_zeta_pow_sub_one_associated D 34 (by decide)
  have h_dvd : (D.hζ.toInteger - 1 : 𝓞 K) ∣ (D.hζ.toInteger : 𝓞 K) ^ 34 - 1 := h_assoc.symm.dvd
  rw [sq]
  exact mul_dvd_mul (dvd_refl _) (Dvd.dvd.mul_left h_dvd _)

/-- **`(ζ - 1) ∣ Q_2 = D.x² + D.x·D.y·γ_2 + D.y²` via the factored form.** Since
`Q_2 = (D.x + D.y·η_2)(D.x + D.y·η_2^36) = 𝔪·𝔭·𝔠(η_2)·𝔪·𝔭·𝔠(η_2^36)` has `𝔭` as a divisor
of each factor (from `m_mul_c_mul_p`), `(ζ-1)` divides `D.x + D.y·η_2` and hence Q_2. -/
theorem caseII_K_zeta_sub_one_dvd_symmetric_at_etaTwo {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣
      D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2 := by
  rw [← caseII_pair_product_symmetric_expansion D D.etaTwo]
  have h_dvd : (D.hζ.toInteger - 1 : 𝓞 K) ∣ D.x + D.y * (D.etaTwo : 𝓞 K) := by
    rw [← Ideal.mem_span_singleton]
    have h_eq := m_mul_c_mul_p hp D.hζ D.equation D.hy D.etaTwo
    have h_mem : D.x + D.y * (D.etaTwo : 𝓞 K) ∈ Ideal.span ({D.x + D.y * (D.etaTwo : 𝓞 K)} :
        Set (𝓞 K)) := Ideal.mem_span_singleton_self _
    rw [← h_eq] at h_mem
    have h_le : gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaTwo *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≤
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
      Ideal.mul_le_left
    exact h_le h_mem
  exact h_dvd.mul_right _

/-- **`(ζ - 1) ∣ D.x + D.y·η_2^36`** (the σ-conjugate factor). -/
theorem caseII_K_zeta_sub_one_dvd_x_add_y_etaTwoInv {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣ D.x + D.y * (D.etaTwo : 𝓞 K) ^ 36 := by
  have h_inv_coe : (D.etaTwo : 𝓞 K) ^ 36 = (caseII_etaInv D.etaTwo : 𝓞 K) := rfl
  rw [h_inv_coe, ← Ideal.mem_span_singleton]
  have h_eq := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv D.etaTwo)
  have h_mem : D.x + D.y * (caseII_etaInv D.etaTwo : 𝓞 K) ∈
      Ideal.span ({D.x + D.y * (caseII_etaInv D.etaTwo : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.mem_span_singleton_self _
  rw [← h_eq] at h_mem
  have h_le : gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
      divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaTwo) *
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≤
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.mul_le_left
  exact h_le h_mem

/-- **`(ζ - 1)² ∣ Q_2`.** Combining the two single-factor divisibilities. -/
theorem caseII_K_zeta_sub_one_sq_dvd_symmetric_at_etaTwo {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣
      D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2 := by
  rw [← caseII_pair_product_symmetric_expansion D D.etaTwo, sq]
  refine mul_dvd_mul ?_ ?_
  · -- (ζ-1) ∣ (D.x + D.y·η_2):
    rw [← Ideal.mem_span_singleton]
    have h_eq := m_mul_c_mul_p hp D.hζ D.equation D.hy D.etaTwo
    have h_mem : D.x + D.y * (D.etaTwo : 𝓞 K) ∈
        Ideal.span ({D.x + D.y * (D.etaTwo : 𝓞 K)} : Set (𝓞 K)) :=
      Ideal.mem_span_singleton_self _
    rw [← h_eq] at h_mem
    have h_le : gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaTwo *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≤
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
      Ideal.mul_le_left
    exact h_le h_mem
  · -- (ζ-1) ∣ (D.x + D.y·η_2^36):
    exact caseII_K_zeta_sub_one_dvd_x_add_y_etaTwoInv D hp

/-- **`(ζ - 1)² ∣ Q_1`.** Same proof as `caseII_K_zeta_sub_one_sq_dvd_symmetric_at_etaTwo` at
`η = etaOne`. -/
theorem caseII_K_zeta_sub_one_sq_dvd_symmetric_at_etaOne {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣
      D.x ^ 2 + D.x * D.y * ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) + D.y ^ 2 := by
  rw [← caseII_pair_product_symmetric_expansion D D.etaOne, sq]
  refine mul_dvd_mul ?_ ?_
  · rw [← Ideal.mem_span_singleton]
    have h_eq := m_mul_c_mul_p hp D.hζ D.equation D.hy D.etaOne
    have h_mem : D.x + D.y * (D.etaOne : 𝓞 K) ∈
        Ideal.span ({D.x + D.y * (D.etaOne : 𝓞 K)} : Set (𝓞 K)) :=
      Ideal.mem_span_singleton_self _
    rw [← h_eq] at h_mem
    have h_le : gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaOne *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≤
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
      Ideal.mul_le_left
    exact h_le h_mem
  · have h_inv_coe : (D.etaOne : 𝓞 K) ^ 36 = (caseII_etaInv D.etaOne : 𝓞 K) := rfl
    rw [h_inv_coe, ← Ideal.mem_span_singleton]
    have h_eq := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv D.etaOne)
    have h_mem : D.x + D.y * (caseII_etaInv D.etaOne : 𝓞 K) ∈
        Ideal.span ({D.x + D.y * (caseII_etaInv D.etaOne : 𝓞 K)} : Set (𝓞 K)) :=
      Ideal.mem_span_singleton_self _
    rw [← h_eq] at h_mem
    have h_le : gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaOne) *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≤
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
      Ideal.mul_le_left
    exact h_le h_mem

/-- **`(ζ-1)^(37m+1) ∣ (D.x + D.y)`** in `RealCaseIIData37`. Direct from
`caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero` + `D.etaZero = 1` (`caseII_etaZero_eq_one`):
`(ζ-1)^(37m+1) ∣ (D.x + D.y · 1) = D.x + D.y`. -/
theorem caseII_K_zeta_sub_one_pow_dvd_x_add_y {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) ∣ D.x + D.y := by
  have h_orig := caseII_zetaSubOne_pow_dvd_x_add_y_mul_etaZero D hp
  have h_etaZero := caseII_etaZero_eq_one D hp
  rwa [h_etaZero, mul_one] at h_orig

/-- **K⁺-pair-realGenerator at the anchor is `(xP + yP)²`.** Under `D.etaZero = 1`, the
K⁺-trace at the anchor is `caseII_eta_trace D.etaZero = 1 + 1 = 2`, so
`P_K⁺_η₀ = xP² + xP·yP·2 + yP² = (xP + yP)²`. -/
theorem caseII_data_pair_realGenerator_at_etaZero_eq_xP_plus_yP_sq {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator D D.etaZero =
      (caseII_data_xP D + caseII_data_yP D) ^ 2 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  change caseII_data_pair_realGenerator_K D D.etaZero = _
  rw [caseII_data_pair_realGenerator_K_eq, caseII_etaZero_eq_one D hp]
  push_cast [caseII_data_xP_spec, caseII_data_yP_spec]
  ring

/-- **K-level pair-realGenerator at the anchor is `(D.x + D.y)²`.** Direct from
`caseII_data_pair_realGenerator_K_eq` + `D.etaZero = 1`. -/
theorem caseII_data_pair_realGenerator_K_at_etaZero_eq_sq {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator_K D D.etaZero = (D.x + D.y) ^ 2 := by
  rw [caseII_data_pair_realGenerator_K_eq, caseII_etaZero_eq_one D hp]
  ring

/-- **Anchor pair-ideal is a perfect square**: `𝔞(D.etaZero) · 𝔞(caseII_etaInv D.etaZero) =
𝔞(D.etaZero) · 𝔞(D.etaZero) = 𝔞(D.etaZero)²`. Using `caseII_etaInv_etaZero_eq_etaZero`. -/
theorem caseII_anchor_pair_ideal_eq_sq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero) =
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero) ^ 2 := by
  rw [caseII_etaInv_etaZero_eq_etaZero D hp, sq]

/-- **`𝔭^m ∣ 𝔞(D.etaZero)·𝔞(D.etaZero)/𝔪² = 𝔞(D.etaZero)²/𝔪²` (`p_pow_dvd_a_eta_zero` squared).**
The anchor pair has 𝔭-content ≥ 2m (already shipped as `caseII_p_pow_two_m_dvd_pair_at_etaZero`)
but now expressed via the simplified perfect-square form. -/
theorem caseII_p_pow_two_m_dvd_anchor_sq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) ∣
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero) ^ 2 := by
  rw [← caseII_anchor_pair_ideal_eq_sq D hp]
  exact caseII_p_pow_two_m_dvd_pair_at_etaZero D hp

/-- **`𝔭^m ∣ 𝔞(D.etaZero)` via 𝔭^(2m) ∣ 𝔞².** Via ideal-level UFM
(`UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd`). Recovers the original
`caseII_p_pow_dvd_a_etaZero` from the squared form. -/
theorem caseII_p_pow_dvd_anchor_via_sq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero := by
  have h_sq := caseII_p_pow_two_m_dvd_anchor_sq D hp
  have h_pow_eq : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (2 * m) =
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm m 2]
  rw [h_pow_eq] at h_sq
  exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 2) (by norm_num)).mp h_sq

/-- **σ-stable cross identity simplified using anchor = square**: from the perfect-square
form `𝔞(η₀)·𝔞(η₀⁻¹) = 𝔞(η₀)²`, the cross identity reads
`span(x)·𝔞(η)·𝔞(η⁻¹) = span(y)·𝔞(η₀)²`. -/
theorem caseII_sigma_pair_anchored_cross_eq_with_anchor_sq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus} *
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) =
      Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus} *
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero) ^ 2 := by
  rw [← caseII_anchor_pair_ideal_eq_sq D hp]
  exact G.cross_eq

/-- **K-level identity simplified using anchor = `(D.x + D.y)²`.** From
`caseII_sigma_pair_pow37_K_plus_identity` + `caseII_data_pair_realGenerator_K_at_etaZero_eq_sq`:
`(algebraMap x)^37 · pair_realGenerator_K η · u = (algebraMap y)^37 · (D.x + D.y)²`. -/
theorem caseII_sigma_pair_pow37_K_anchor_sq {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
        caseII_data_pair_realGenerator_K D η *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
        (D.x + D.y) ^ 2 := by
  obtain ⟨u_KP, h⟩ := caseII_sigma_pair_pow37_K_plus_identity D hp η G
  refine ⟨u_KP, ?_⟩
  have h_K := congrArg (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) h
  simp only [map_mul, map_pow] at h_K
  rw [show (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
        (caseII_data_pair_realGenerator D D.etaZero) = (D.x + D.y) ^ 2 from
      caseII_data_pair_realGenerator_K_at_etaZero_eq_sq D hp] at h_K
  exact h_K

/-- **K⁺-level identity with `(xP + yP)²` form**: substituting
`caseII_data_pair_realGenerator_at_etaZero_eq_xP_plus_yP_sq` gives
`xPlus^37 · pair_realGenerator η · u = yPlus^37 · (xP + yP)²` in 𝓞 K⁺. -/
theorem caseII_sigma_pair_pow37_K_plus_anchor_xP_plus_yP_sq {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      G.xPlus ^ 37 * caseII_data_pair_realGenerator D η * (u_KP : 𝓞 _) =
      G.yPlus ^ 37 * (caseII_data_xP D + caseII_data_yP D) ^ 2 := by
  obtain ⟨u_KP, h⟩ := caseII_sigma_pair_pow37_K_plus_identity D hp η G
  refine ⟨u_KP, ?_⟩
  rwa [caseII_data_pair_realGenerator_at_etaZero_eq_xP_plus_yP_sq D hp] at h

/-- **`xP + yP ≠ 0` in 𝓞 K⁺.** Direct from `caseII_data_pair_realGenerator_ne_zero D hp D.etaZero =
(xP + yP)² ≠ 0` and integral domain. -/
theorem caseII_data_xP_add_yP_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    caseII_data_xP D + caseII_data_yP D ≠ 0 := by
  intro h_zero
  have h_sq_ne_zero : caseII_data_pair_realGenerator D D.etaZero ≠ 0 :=
    caseII_data_pair_realGenerator_ne_zero D hp D.etaZero
  rw [caseII_data_pair_realGenerator_at_etaZero_eq_xP_plus_yP_sq D hp, h_zero] at h_sq_ne_zero
  simp at h_sq_ne_zero

/-- **`D.x + D.y ≠ 0` in 𝓞 K.** Either from `caseII_data_xP_add_yP_ne_zero` + algebraMap
injectivity,
or directly from `(D.x + D.y) = algebraMap (xP + yP)` and the K⁺-injectivity. -/
theorem caseII_data_x_add_y_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    D.x + D.y ≠ 0 := by
  have h_x : D.x = algebraMap _ (𝓞 K) (caseII_data_xP D) := (caseII_data_xP_spec D).symm
  have h_y : D.y = algebraMap _ (𝓞 K) (caseII_data_yP D) := (caseII_data_yP_spec D).symm
  rw [h_x, h_y, ← map_add]
  intro h_zero
  have h_xP_yP_zero : caseII_data_xP D + caseII_data_yP D = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    rw [h_zero, map_zero]
  exact caseII_data_xP_add_yP_ne_zero D hp h_xP_yP_zero

/-- **`(D.x + D.y)² ≠ 0` in 𝓞 K.** Direct from `D.x + D.y ≠ 0` + integral domain. -/
theorem caseII_data_x_add_y_sq_ne_zero {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.x + D.y) ^ 2 ≠ 0 :=
  pow_ne_zero _ (caseII_data_x_add_y_ne_zero D hp)

/-- **`algebraMap (xP + yP) = D.x + D.y`** — the K-level lift of the K⁺-anchor real generator. -/
theorem caseII_algebraMap_xP_add_yP_eq_x_add_y {m : ℕ} (D : RealCaseIIData37 K m) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_data_xP D + caseII_data_yP D) = D.x + D.y := by
  rw [map_add, caseII_data_xP_spec, caseII_data_yP_spec]

/-- **`(ζ-1)^(74m+2) ∣ (D.x + D.y)²`.** Direct from `(ζ-1)^(37m+1) ∣ (D.x + D.y)` via squaring. -/
theorem caseII_zeta_sub_one_pow_dvd_x_add_y_sq_via_pow_eq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) ∣ (D.x + D.y) ^ 2 := by
  have h_x_add_y := caseII_K_zeta_sub_one_pow_dvd_x_add_y D hp
  have h_sq : ((D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1)) ^ 2 ∣ (D.x + D.y) ^ 2 :=
    pow_dvd_pow_of_dvd h_x_add_y 2
  rw [← pow_mul] at h_sq
  have h_eq : (37 * m + 1) * 2 = 74 * m + 2 := by ring
  rwa [h_eq] at h_sq

/-- **`(ζ-1)^(74m+2) ∣ (algebraMap yPlus)^37 · (D.x + D.y)²`** — combining the divisibility of
`(D.x + D.y)²` with the multiplicativity. -/
theorem caseII_zeta_sub_one_pow_dvd_yPlus_pow_times_sq {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) ∣
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.yPlus) ^ 37 *
        (D.x + D.y) ^ 2 :=
  (caseII_zeta_sub_one_pow_dvd_x_add_y_sq_via_pow_eq D hp).mul_left _

/-- **`(ζ-1)^(74m+2) ∣ (algebraMap xPlus)^37 · P_K_η · algebraMap u_KP`** — derived from the K-level
identity `(algebraMap xPlus)^37 · P_K_η · u_K = (algebraMap yPlus)^37 · (D.x + D.y)²` and the
RHS divisibility. -/
theorem caseII_zeta_sub_one_pow_dvd_LHS {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) ∣
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
          caseII_data_pair_realGenerator_K D η *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)) := by
  obtain ⟨u_KP, h⟩ := caseII_sigma_pair_pow37_K_anchor_sq D hp η G
  refine ⟨u_KP, ?_⟩
  rw [h]
  exact caseII_zeta_sub_one_pow_dvd_yPlus_pow_times_sq D hp η G

/-- **`(ζ-1) ∣ D.x + D.y · η` for any 37-th root η.** Each factor `D.x + D.y · η` lies in 𝔭
via `m_mul_c_mul_p`, regardless of whether η = D.etaZero or not. -/
theorem caseII_K_zeta_sub_one_dvd_x_add_y_times_root {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣ D.x + D.y * (η : 𝓞 K) := by
  rw [← Ideal.mem_span_singleton]
  have h_eq := m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have h_mem : D.x + D.y * (η : 𝓞 K) ∈
      Ideal.span ({D.x + D.y * (η : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.mem_span_singleton_self _
  rw [← h_eq] at h_mem
  have h_le : gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
      divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≤
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.mul_le_left
  exact h_le h_mem

/-- **`(ζ-1)² ∣ P_K_η`** for any 37-th root η. -/
theorem caseII_K_zeta_sub_one_sq_dvd_pair_realGenerator_K {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ caseII_data_pair_realGenerator_K D η := by
  rw [caseII_data_pair_realGenerator_K_eq]
  have h1 : (D.hζ.toInteger - 1 : 𝓞 K) ∣ D.x + D.y * (η : 𝓞 K) :=
    caseII_K_zeta_sub_one_dvd_x_add_y_times_root D hp η
  have h2 : (D.hζ.toInteger - 1 : 𝓞 K) ∣ D.x + D.y * (η : 𝓞 K) ^ 36 := by
    have h_inv : (η : 𝓞 K) ^ 36 = (caseII_etaInv η : 𝓞 K) := rfl
    rw [h_inv]
    exact caseII_K_zeta_sub_one_dvd_x_add_y_times_root D hp (caseII_etaInv η)
  rw [sq]
  exact mul_dvd_mul h1 h2

/-- **`algebraMap Λ ∣ P_K_η`** for any 37-th root η: combining `Associated (algebraMap Λ) (ζ-1)²`
+ `(ζ-1)² ∣ P_K_η`. -/
theorem caseII_K_algebraMap_LambdaCyc_dvd_pair_realGenerator_K {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) ∣
      caseII_data_pair_realGenerator_K D η := by
  have h_assoc := caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D
  have h_sq_dvd := caseII_K_zeta_sub_one_sq_dvd_pair_realGenerator_K D hp η
  exact h_assoc.dvd.trans h_sq_dvd

/-- **`Λ ∣ pair_realGenerator D η`** for any η, in 𝓞 K⁺. The K⁺-level analog of
`caseII_K_algebraMap_LambdaCyc_dvd_pair_realGenerator_K`. Uses σ-fixedness:
the quotient `(algebraMap pair_realGenerator)/(algebraMap Λ) ∈ K` is σ-fixed (both numerator
and denominator are), so descends to a K⁺-element. -/
theorem caseII_LambdaCyc_dvd_pair_realGenerator_general {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_LambdaCyc D ∣ caseII_data_pair_realGenerator D η := by
  have h_K : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_LambdaCyc D) ∣
      caseII_data_pair_realGenerator_K D η :=
    caseII_K_algebraMap_LambdaCyc_dvd_pair_realGenerator_K D hp η
  obtain ⟨c, hc⟩ := h_K
  have h_z_real : caseII_data_pair_realGenerator_K D η ∈
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
    ⟨caseII_data_pair_realGenerator D η, rfl⟩
  have h_Λ_real : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_LambdaCyc D) ∈
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
    ⟨caseII_LambdaCyc D, rfl⟩
  have h_z_fixed : NumberField.IsCMField.ringOfIntegersComplexConj K
      (caseII_data_pair_realGenerator_K D η) = caseII_data_pair_realGenerator_K D η :=
    (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mpr h_z_real
  have h_Λ_fixed : NumberField.IsCMField.ringOfIntegersComplexConj K
      (algebraMap _ (𝓞 K) (caseII_LambdaCyc D)) =
      algebraMap _ (𝓞 K) (caseII_LambdaCyc D) :=
    (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) _).mpr h_Λ_real
  have h_σ := congrArg (NumberField.IsCMField.ringOfIntegersComplexConj K) hc
  rw [map_mul, h_z_fixed, h_Λ_fixed] at h_σ
  have h_Λ_ne_zero : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
      (caseII_LambdaCyc D) ≠ 0 := caseII_LambdaCyc_algebraMap_ne_zero D
  have h_c_fixed : NumberField.IsCMField.ringOfIntegersComplexConj K c = c := by
    have h_eq : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) *
        (NumberField.IsCMField.ringOfIntegersComplexConj K) c =
        algebraMap _ _ (caseII_LambdaCyc D) * c := h_σ.symm.trans hc
    exact mul_left_cancel₀ h_Λ_ne_zero h_eq
  obtain ⟨c', hc'⟩ := (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff
      (K := K) c).mp h_c_fixed
  refine ⟨c', ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [map_mul, hc']
  change caseII_data_pair_realGenerator_K D η =
    algebraMap _ (𝓞 K) (caseII_LambdaCyc D) * c
  exact hc

/-- **The K⁺-pair-realGenerator-divided-by-Λ for general η**: concrete witness for
`Λ ∣ pair_realGenerator D η`. -/
noncomputable def caseII_pair_realGenerator_div_LambdaCyc_general {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (caseII_LambdaCyc_dvd_pair_realGenerator_general D hp η).choose

/-- **Spec for `caseII_pair_realGenerator_div_LambdaCyc_general`.** -/
@[simp] theorem caseII_pair_realGenerator_div_LambdaCyc_general_spec {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_data_pair_realGenerator D η =
      caseII_LambdaCyc D * caseII_pair_realGenerator_div_LambdaCyc_general D hp η :=
  (caseII_LambdaCyc_dvd_pair_realGenerator_general D hp η).choose_spec

/-- **`Λ ≠ 0` in 𝓞 K⁺.** Direct from `caseII_LambdaCyc_ne_zero`. -/
theorem caseII_LambdaCyc_ne_zero_K_plus {m : ℕ} (D : RealCaseIIData37 K m) :
    caseII_LambdaCyc D ≠ 0 := caseII_LambdaCyc_ne_zero D

/-- **K⁺-level cross identity rewritten with Λ-quotient at η.** Substituting
`pair_realGenerator D η = Λ · Q_η` into the K⁺-level identity gives:
`xPlus^37 · Λ · Q_η · u_KP = yPlus^37 · pair_realGenerator D etaZero`. -/
theorem caseII_sigma_pair_pow37_K_plus_LambdaCyc_at_eta {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      G.xPlus ^ 37 * (caseII_LambdaCyc D *
          caseII_pair_realGenerator_div_LambdaCyc_general D hp η) *
        (u_KP : 𝓞 _) =
      G.yPlus ^ 37 * caseII_data_pair_realGenerator D D.etaZero := by
  obtain ⟨u_KP, h⟩ := caseII_sigma_pair_pow37_K_plus_identity D hp η G
  refine ⟨u_KP, ?_⟩
  rw [← caseII_pair_realGenerator_div_LambdaCyc_general_spec D hp η]
  exact h

/-- **K⁺-level cross identity with Λ-decomposition on both sides**: substituting
`pair_realGenerator at η = Λ · Q_η` and `pair_realGenerator etaZero = Λ^(37m+1) · Q_etaZero`
into the K⁺-level identity gives:
`xPlus^37 · Λ · Q_η · u_KP = yPlus^37 · Λ^(37m+1) · Q_etaZero`. -/
theorem caseII_sigma_pair_pow37_K_plus_LambdaCyc_decomposition {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      G.xPlus ^ 37 * (caseII_LambdaCyc D *
          caseII_pair_realGenerator_div_LambdaCyc_general D hp η) *
        (u_KP : 𝓞 _) =
      G.yPlus ^ 37 * (caseII_LambdaCyc D ^ (37 * m + 1) *
        caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp) := by
  obtain ⟨u_KP, h⟩ := caseII_sigma_pair_pow37_K_plus_LambdaCyc_at_eta D hp η G
  refine ⟨u_KP, ?_⟩
  rwa [caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow_spec D hp] at h

/-- **K⁺-level cross identity after canceling Λ from both sides**: starting from
`xPlus^37 · Λ · Q_η · u_KP = yPlus^37 · Λ^(37m+1) · Q_etaZero` and canceling Λ ≠ 0:
`xPlus^37 · Q_η · u_KP = yPlus^37 · Λ^(37m) · Q_etaZero`. The Λ-power on the right is the
"uniformizer power" of the σ-stable descent. -/
theorem caseII_sigma_pair_pow37_K_plus_LambdaCyc_canceled {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      G.xPlus ^ 37 * caseII_pair_realGenerator_div_LambdaCyc_general D hp η *
        (u_KP : 𝓞 _) =
      G.yPlus ^ 37 * (caseII_LambdaCyc D ^ (37 * m) *
        caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp) := by
  obtain ⟨u_KP, h⟩ := caseII_sigma_pair_pow37_K_plus_LambdaCyc_decomposition D hp η G
  refine ⟨u_KP, ?_⟩
  have h_Λ_ne_zero : caseII_LambdaCyc D ≠ 0 := caseII_LambdaCyc_ne_zero D
  apply mul_left_cancel₀ h_Λ_ne_zero
  have h_LHS_eq : caseII_LambdaCyc D *
      (G.xPlus ^ 37 * caseII_pair_realGenerator_div_LambdaCyc_general D hp η *
        (u_KP : 𝓞 _)) =
      G.xPlus ^ 37 * (caseII_LambdaCyc D *
        caseII_pair_realGenerator_div_LambdaCyc_general D hp η) *
      (u_KP : 𝓞 _) := by ring
  have h_RHS_eq : caseII_LambdaCyc D *
      (G.yPlus ^ 37 * (caseII_LambdaCyc D ^ (37 * m) *
        caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp)) =
      G.yPlus ^ 37 * (caseII_LambdaCyc D ^ (37 * m + 1) *
        caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp) := by
    rw [show (37 * m + 1 : ℕ) = 37 * m + 1 from rfl, pow_succ]
    ring
  rw [h_LHS_eq, h_RHS_eq]
  exact h

/-- **`Λ^(37m) ∣ xPlus^37 · Q_η · u_KP`** — direct from the Λ-canceled K⁺-level identity. -/
theorem caseII_LambdaCyc_pow_dvd_xPlus_pow_times_Q {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      caseII_LambdaCyc D ^ (37 * m) ∣
        G.xPlus ^ 37 * caseII_pair_realGenerator_div_LambdaCyc_general D hp η *
          (u_KP : 𝓞 _) := by
  obtain ⟨u_KP, h⟩ := caseII_sigma_pair_pow37_K_plus_LambdaCyc_canceled D hp η G
  refine ⟨u_KP, ?_⟩
  rw [h]
  use G.yPlus ^ 37 * caseII_pair_realGenerator_at_etaZero_div_LambdaCyc_pow D hp
  ring

/-- **`Q_η ≠ 0`** for any η — follows from `Q_η = pair_realGenerator η / Λ` and both being
nonzero. -/
theorem caseII_pair_realGenerator_div_LambdaCyc_general_ne_zero {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_pair_realGenerator_div_LambdaCyc_general D hp η ≠ 0 := by
  intro h_zero
  have h_spec := caseII_pair_realGenerator_div_LambdaCyc_general_spec D hp η
  rw [h_zero, mul_zero] at h_spec
  exact caseII_data_pair_realGenerator_ne_zero D hp η h_spec

/-- **`(algebraMap Λ)^(37m) ∣ (algebraMap xPlus)^37 · algebraMap Q_η · algebraMap u_KP` in 𝓞 K**:
the K-level analog of `caseII_LambdaCyc_pow_dvd_xPlus_pow_times_Q`. -/
theorem caseII_algebraMap_LambdaCyc_pow_dvd_K_LHS {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D)) ^ (37 * m) ∣
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G.xPlus) ^ 37 *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (caseII_pair_realGenerator_div_LambdaCyc_general D hp η)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u_KP : 𝓞 _)) := by
  obtain ⟨u_KP, h⟩ := caseII_LambdaCyc_pow_dvd_xPlus_pow_times_Q D hp η G
  refine ⟨u_KP, ?_⟩
  obtain ⟨k, hk⟩ := h
  use algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) k
  have h_K := congrArg (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) hk
  simp only [map_mul, map_pow] at h_K
  exact h_K

/-- **`Λ ≠ ⊥ as a K⁺-ideal`.** -/
theorem caseII_span_LambdaCyc_ne_bot {m : ℕ} (D : RealCaseIIData37 K m) :
    Ideal.span ({caseII_LambdaCyc D} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact caseII_LambdaCyc_ne_zero D

/-- **`span(Λ)^(37m) ∣ span(xPlus^37 · Q_η · u_KP) in 𝓞 K⁺`** — ideal-level lift of
`caseII_LambdaCyc_pow_dvd_xPlus_pow_times_Q`. -/
theorem caseII_span_LambdaCyc_pow_dvd_K_plus_LHS_span {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    ∃ u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      Ideal.span ({caseII_LambdaCyc D} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) ^ (37 * m) ∣
        Ideal.span ({G.xPlus ^ 37 *
          caseII_pair_realGenerator_div_LambdaCyc_general D hp η *
          (u_KP : 𝓞 _)} : Set (𝓞 (NumberField.maximalRealSubfield K))) := by
  obtain ⟨u_KP, h⟩ := caseII_LambdaCyc_pow_dvd_xPlus_pow_times_Q D hp η G
  refine ⟨u_KP, ?_⟩
  have h_le : Ideal.span ({G.xPlus ^ 37 *
      caseII_pair_realGenerator_div_LambdaCyc_general D hp η * (u_KP : 𝓞 _)} :
      Set (𝓞 (NumberField.maximalRealSubfield K))) ≤
      Ideal.span ({caseII_LambdaCyc D ^ (37 * m)} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) :=
    Ideal.span_singleton_le_span_singleton.mpr h
  have h_pow : Ideal.span ({caseII_LambdaCyc D ^ (37 * m)} :
      Set (𝓞 (NumberField.maximalRealSubfield K))) =
      Ideal.span ({caseII_LambdaCyc D} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ^ (37 * m) :=
    (Ideal.span_singleton_pow _ _).symm
  rw [h_pow] at h_le
  exact Ideal.dvd_iff_le.mpr h_le

/-- **`span(xPlus^37 · Q_η · u_KP) = span(xPlus)^37 · span(Q_η)`** since `u_KP` is a unit. -/
theorem caseII_span_LHS_factored {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η)
    (u_KP : (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
    Ideal.span ({G.xPlus ^ 37 *
        caseII_pair_realGenerator_div_LambdaCyc_general D hp η * (u_KP : 𝓞 _)} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) =
      Ideal.span ({G.xPlus} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) ^ 37 *
        Ideal.span ({caseII_pair_realGenerator_div_LambdaCyc_general D hp η} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) := by
  rw [Ideal.span_singleton_mul_right_unit u_KP.isUnit,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]

/-- **`span(Λ)^(37m) ∣ span(xPlus)^37 · span(Q_η)`** — the factored form of the ideal-level
Λ-divisibility on the LHS. -/
theorem caseII_span_LambdaCyc_pow_dvd_K_plus_LHS_factored {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    Ideal.span ({caseII_LambdaCyc D} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ^ (37 * m) ∣
      Ideal.span ({G.xPlus} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) ^ 37 *
        Ideal.span ({caseII_pair_realGenerator_div_LambdaCyc_general D hp η} :
          Set (𝓞 (NumberField.maximalRealSubfield K))) := by
  obtain ⟨u_KP, h⟩ := caseII_span_LambdaCyc_pow_dvd_K_plus_LHS_span D hp η G
  rwa [caseII_span_LHS_factored D hp η G u_KP] at h

/-- **`span(xPlus) ≠ ⊥`** — direct from `xPlus ≠ 0`. -/
theorem caseII_span_xPlus_ne_bot {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    Ideal.span ({G.xPlus} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact G.xPlus_ne_zero

/-- **`span(Q_η) ≠ ⊥`** — direct from `Q_η ≠ 0`. -/
theorem caseII_span_Q_eta_ne_bot {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    Ideal.span ({caseII_pair_realGenerator_div_LambdaCyc_general D hp η} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact caseII_pair_realGenerator_div_LambdaCyc_general_ne_zero D hp η

/-- **`span(yPlus) ≠ ⊥`** — direct from `yPlus ≠ 0`. -/
theorem caseII_span_yPlus_ne_bot {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D hp η) :
    Ideal.span ({G.yPlus} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact G.yPlus_ne_zero

/-- **`Λ` is not a unit in `𝓞 K⁺`.** Direct from `algebraMap Λ ~ (ζ-1)²` being non-unit
(since `(ζ-1)` is prime in `𝓞 K` and `(ζ-1)² ∼ Λ.algebraMap` is non-unit). -/
theorem caseII_LambdaCyc_not_isUnit {m : ℕ} (D : RealCaseIIData37 K m) :
    ¬ IsUnit (caseII_LambdaCyc D) := by
  intro h_unit
  have h_K_unit : IsUnit (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
      (caseII_LambdaCyc D)) :=
    h_unit.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
  have h_assoc := caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D
  have h_sq_unit : IsUnit ((D.hζ.toInteger - 1 : 𝓞 K) ^ 2) := by
    rw [← h_assoc.isUnit_iff]
    exact h_K_unit
  have h_zeta_unit : IsUnit (D.hζ.toInteger - 1 : 𝓞 K) := by
    rcases (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h_sq_unit with h
    exact h
  exact D.hζ.zeta_sub_one_prime'.not_unit h_zeta_unit

/-- **`Ideal.span {Λ} ≠ ⊤` in `𝓞 K⁺`.** Direct from `Λ` not being a unit. -/
theorem caseII_span_LambdaCyc_ne_top {m : ℕ} (D : RealCaseIIData37 K m) :
    Ideal.span ({caseII_LambdaCyc D} :
        Set (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊤ := by
  intro h
  rw [Ideal.eq_top_iff_one] at h
  rw [Ideal.mem_span_singleton] at h
  exact caseII_LambdaCyc_not_isUnit D (isUnit_of_dvd_one h)

/-- **`(ζ - 1) ∣ algebraMap Λ` in `𝓞 K`.** Direct from `Associated (algebraMap Λ) ((ζ-1)²)`
+ `(ζ-1) ∣ (ζ-1)²`. -/
theorem caseII_K_zeta_sub_one_dvd_algebraMap_LambdaCyc {m : ℕ} (D : RealCaseIIData37 K m) :
    (D.hζ.toInteger - 1 : 𝓞 K) ∣
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) := by
  have h_assoc := caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D
  have h_dvd : (D.hζ.toInteger - 1 : 𝓞 K) ∣ (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 :=
    dvd_pow_self _ (by norm_num)
  exact h_dvd.trans h_assoc.symm.dvd

/-- **`(ζ - 1)² ∣ algebraMap Λ` in `𝓞 K`.** Direct from
`Associated (algebraMap Λ) ((ζ-1)²)`. -/
theorem caseII_K_zeta_sub_one_sq_dvd_algebraMap_LambdaCyc {m : ℕ} (D : RealCaseIIData37 K m) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (caseII_LambdaCyc D) :=
  (caseII_LambdaCyc_algebraMap_associated_zeta_sub_one_sq D).symm.dvd

/-- **`(ζ - 1)^(2k) ∣ (algebraMap Λ)^k`** for any k. Power version of
`caseII_K_zeta_sub_one_sq_dvd_algebraMap_LambdaCyc`. -/
theorem caseII_K_zeta_sub_one_pow_dvd_algebraMap_LambdaCyc_pow {m : ℕ}
    (D : RealCaseIIData37 K m) (k : ℕ) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (2 * k) ∣
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_LambdaCyc D)) ^ k := by
  have h_base := caseII_K_zeta_sub_one_sq_dvd_algebraMap_LambdaCyc D
  have h_pow_k := pow_dvd_pow_of_dvd h_base k
  rw [show (D.hζ.toInteger - 1 : 𝓞 K) ^ (2 * k) = ((D.hζ.toInteger - 1 : 𝓞 K) ^ 2) ^ k by
    rw [← pow_mul]]
  exact h_pow_k

/-- **`(ζ - 1)^(2k) ∣ algebraMap (Λ^k)`** — the previous lemma rewritten with algebraMap
distributed. -/
theorem caseII_K_zeta_sub_one_pow_dvd_algebraMap_LambdaCyc_pow_v2 {m : ℕ}
    (D : RealCaseIIData37 K m) (k : ℕ) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (2 * k) ∣
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (caseII_LambdaCyc D ^ k) := by
  rw [map_pow]
  exact caseII_K_zeta_sub_one_pow_dvd_algebraMap_LambdaCyc_pow D k

/-- **Span identity for the K-level adjacent K-pair-realGenerator at D.etaOne**. Direct
expansion via `caseII_data_pair_realGenerator_K_eq`. -/
theorem caseII_data_pair_realGenerator_K_at_etaOne_eq {m : ℕ}
    (D : RealCaseIIData37 K m) (_hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator_K D D.etaOne =
      (D.x + D.y * (D.etaOne : 𝓞 K)) * (D.x + D.y * (D.etaOne : 𝓞 K) ^ 36) :=
  caseII_data_pair_realGenerator_K_eq D D.etaOne

/-- **Span identity for the K-level adjacent K-pair-realGenerator at D.etaTwo**. -/
theorem caseII_data_pair_realGenerator_K_at_etaTwo_eq {m : ℕ}
    (D : RealCaseIIData37 K m) (_hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator_K D D.etaTwo =
      (D.x + D.y * (D.etaTwo : 𝓞 K)) * (D.x + D.y * (D.etaTwo : 𝓞 K) ^ 36) :=
  caseII_data_pair_realGenerator_K_eq D D.etaTwo

/-- **K-level expansion of `D.etaOne = ζ`**. With `D.etaZero = 1`, `D.etaOne = 1·ζ = ζ`. -/
theorem caseII_etaOne_coe_eq_zeta {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.etaOne : 𝓞 K) = D.hζ.toInteger := by
  rw [caseII_etaOne_coe_eq, caseII_etaZero_eq_one D hp, one_mul]

/-- **K-level expansion of `D.etaTwo = ζ²`**. -/
theorem caseII_etaTwo_coe_eq_zeta_sq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.etaTwo : 𝓞 K) = D.hζ.toInteger * D.hζ.toInteger := by
  rw [caseII_etaTwo_coe_eq, caseII_etaZero_eq_one D hp, one_mul]

/-- **K-level identity using etaOne = ζ**: `caseII_data_pair_realGenerator_K D D.etaOne =
(D.x + D.y·ζ)·(D.x + D.y·ζ^36)`. -/
theorem caseII_data_pair_realGenerator_K_at_etaOne_eq_zeta_form {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator_K D D.etaOne =
      (D.x + D.y * D.hζ.toInteger) * (D.x + D.y * D.hζ.toInteger ^ 36) := by
  rw [caseII_data_pair_realGenerator_K_eq, caseII_etaOne_coe_eq_zeta D hp]

/-- **K-level identity using etaTwo = ζ²**: `caseII_data_pair_realGenerator_K D D.etaTwo =
(D.x + D.y·ζ²)·(D.x + D.y·ζ^35)`. (Using `ζ^72 = ζ^35` from `ζ^37 = 1`.) -/
theorem caseII_data_pair_realGenerator_K_at_etaTwo_eq_zeta_sq_form {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_data_pair_realGenerator_K D D.etaTwo =
      (D.x + D.y * D.hζ.toInteger ^ 2) * (D.x + D.y * D.hζ.toInteger ^ 35) := by
  rw [caseII_data_pair_realGenerator_K_eq, caseII_etaTwo_coe_eq_zeta_sq D hp]
  have hζ37 : (D.hζ.toInteger : 𝓞 K) ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have h_72_eq_35 : (D.hζ.toInteger : 𝓞 K) ^ 72 = D.hζ.toInteger ^ 35 := by
    have : (D.hζ.toInteger : 𝓞 K) ^ 72 = (D.hζ.toInteger ^ 37) * D.hζ.toInteger ^ 35 := by ring
    rw [this, hζ37, one_mul]
  have h_sq : D.hζ.toInteger * D.hζ.toInteger = D.hζ.toInteger ^ 2 := by ring
  rw [h_sq]
  congr 1
  rw [show ((D.hζ.toInteger : 𝓞 K) ^ 2) ^ 36 = D.hζ.toInteger ^ 72 by ring, h_72_eq_35]

/-- **K-level adjacent identity fully expanded in ζ-form**: with D.etaZero = 1, the K-level
two-root identity becomes:
`A^37 · (D.x + D.y·ζ)·(D.x + D.y·ζ^36) · algebraMap u₁ =
B^37 · (D.x + D.y·ζ²)·(D.x + D.y·ζ^35) · algebraMap u₂`. -/
theorem caseII_sigma_pair_pow37_K_adjacent_zeta_expanded {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₂.yPlus * G₁.xPlus)) ^ 37 *
        ((D.x + D.y * D.hζ.toInteger) * (D.x + D.y * D.hζ.toInteger ^ 36)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₁.yPlus * G₂.xPlus)) ^ 37 *
        ((D.x + D.y * D.hζ.toInteger ^ 2) * (D.x + D.y * D.hζ.toInteger ^ 35)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) := by
  obtain ⟨u₁, u₂, h⟩ := caseII_sigma_pair_pow37_K_adjacent_identity D hp G₁ G₂
  refine ⟨u₁, u₂, ?_⟩
  rw [← caseII_data_pair_realGenerator_K_eq, ← caseII_data_pair_realGenerator_K_eq] at h
  rwa [caseII_data_pair_realGenerator_K_at_etaOne_eq_zeta_form D hp,
    caseII_data_pair_realGenerator_K_at_etaTwo_eq_zeta_sq_form D hp] at h

/-- **Anchor pair-realGenerator under `D.etaZero = 1`: `(ζ-1)^(74m+2) ∣ (D.x + D.y)²`.** With
`D.etaZero = 1`, `caseII_data_pair_realGenerator_K D D.etaZero = (D.x + D.y)·(D.x + D.y·1^36)
= (D.x + D.y)²`. -/
theorem caseII_K_zeta_sub_one_pow_dvd_x_add_y_sq {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (74 * m + 2) ∣ (D.x + D.y) ^ 2 := by
  have h_orig := caseII_zetaSubOne_pow_dvd_pair_realGenerator_K_at_etaZero D hp
  have h_etaZero := caseII_etaZero_eq_one D hp
  rw [caseII_data_pair_realGenerator_K_eq, h_etaZero] at h_orig
  have h_simp : (D.x + D.y * (1 : 𝓞 K)) * (D.x + D.y * (1 : 𝓞 K) ^ 36) =
      (D.x + D.y) ^ 2 := by ring
  rwa [h_simp] at h_orig

/-- **`(ζ - 1)⁴ ∣ Q_1 · (γ_1 - γ_2)`.** Combining `(ζ-1)² ∣ Q_1` + `(ζ-1)² ∣ (γ_1 - γ_2)`. -/
theorem caseII_K_zeta_sub_one_four_dvd_Q1_times_trace_diff {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 4 ∣
      (D.x ^ 2 + D.x * D.y * ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) + D.y ^ 2) *
        (((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) -
          ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36)) := by
  have h_Q1 := caseII_K_zeta_sub_one_sq_dvd_symmetric_at_etaOne D hp
  have h_diff := caseII_K_zeta_sub_one_sq_dvd_trace_diff D hp
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  exact mul_dvd_mul h_Q1 h_diff

/-- **Combined: Cramer-step + trace factorization.** Substituting the (ζ-1)-factorization of
`γ_1 - γ_2` into the K-level Cramer-step gives:
`Q_2 · (A^37·u_1 - B^37·u_2) = -A^37·u_1·D.x·D.y·(ζ-1)·(η₀^36·ζ^35 - η₀·ζ)`.
This is the form where `(ζ-1)` appears explicitly on the RHS, the immediate input to the
Diekmann descent's 𝔭-uniformizer extraction step. -/
theorem caseII_K_pair_cramer_with_trace_factor {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2) *
          ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
              (G₂.yPlus * G₁.xPlus)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) -
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
              (G₁.yPlus * G₂.xPlus)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _))) =
        -((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (G₂.yPlus * G₁.xPlus)) ^ 37 *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _))) *
          (D.x * D.y * ((D.hζ.toInteger - 1 : 𝓞 K) *
            ((D.etaZero : 𝓞 K) ^ 36 * (D.hζ.toInteger : 𝓞 K) ^ 35 -
              (D.etaZero : 𝓞 K) * D.hζ.toInteger))) := by
  obtain ⟨u₁, u₂, h⟩ := caseII_K_pair_cramer_isolate_xy D hp G₁ G₂
  refine ⟨u₁, u₂, ?_⟩
  rw [← caseII_K_trace_diff_factors D hp]
  exact h

/-- **`(ζ-1) ∣ Q_2 · (A^37·u_1 - B^37·u_2)`.** Immediate from
`caseII_K_pair_cramer_with_trace_factor`: the RHS has `(ζ-1)` as an explicit factor, hence
divides the LHS. The first step toward the Diekmann descent's `(ζ-1)^m`-divisibility extraction. -/
theorem caseII_K_zeta_sub_one_dvd_Q2_times_difference {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (D.hζ.toInteger - 1 : 𝓞 K) ∣
        (D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2) *
          ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
              (G₂.yPlus * G₁.xPlus)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) -
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
              (G₁.yPlus * G₂.xPlus)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _))) := by
  obtain ⟨u₁, u₂, h⟩ := caseII_K_pair_cramer_with_trace_factor D hp G₁ G₂
  refine ⟨u₁, u₂, ?_⟩
  rw [h]
  use -((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (G₂.yPlus * G₁.xPlus)) ^ 37 *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _))) *
      (D.x * D.y *
        ((D.etaZero : 𝓞 K) ^ 36 * (D.hζ.toInteger : 𝓞 K) ^ 35 -
          (D.etaZero : 𝓞 K) * D.hζ.toInteger)
        )
  ring

/-- **Unconditional K-level Cramer-step xy-isolation.** Direct from `RealCaseIIData37 D`
+ Sinnott's `h_VC`, without requiring `G₁, G₂` as parameters (constructed internally via
`caseII_sigma_pair_anchored_fixedGenerator_of_realData`). -/
theorem caseII_K_pair_cramer_isolate_xy_unconditional {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (hη1inv : caseII_etaInv D.etaOne ≠ D.etaZero)
    (hη2inv : caseII_etaInv D.etaTwo ≠ D.etaZero) :
    ∃ (x₁ y₁ x₂ y₂ : 𝓞 (NumberField.maximalRealSubfield K))
      (u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      x₁ ≠ 0 ∧ y₁ ≠ 0 ∧ x₂ ≠ 0 ∧ y₂ ≠ 0 ∧
      (D.x ^ 2 + D.x * D.y * ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) + D.y ^ 2) *
          ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (y₂ * x₁)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) -
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (y₁ * x₂)) ^ 37 *
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _))) =
        -((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (y₂ * x₁)) ^ 37 *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _))) *
          (D.x * D.y * (((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) -
            ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36))) := by
  let G₁ := caseII_sigma_pair_anchored_fixedGenerator_of_realData D hp h_VC D.etaOne
    D.toCaseIIData37.etaOne_ne_etaZero hη1inv
  let G₂ := caseII_sigma_pair_anchored_fixedGenerator_of_realData D hp h_VC D.etaTwo
    D.toCaseIIData37.etaTwo_ne_etaZero hη2inv
  obtain ⟨u₁, u₂, h⟩ := caseII_K_pair_cramer_isolate_xy D hp G₁ G₂
  exact ⟨G₁.xPlus, G₁.yPlus, G₂.xPlus, G₂.yPlus, u₁, u₂,
    G₁.xPlus_ne_zero, G₁.yPlus_ne_zero, G₂.xPlus_ne_zero, G₂.yPlus_ne_zero, h⟩

/-! ### Symmetric Vandermonde descent (the Washington 9.4 consumer for σ-stable pairs)

The σ-stable pair product `Q(η) := (x + yη)(x + yη⁻¹) = x² + xy·γ_η + y²` is **affine** in the
real K-trace `γ_η := η + η⁻¹`. Hence for three roots `η₀, η₁, η₂` the values `Q(η₀), Q(η₁),
Q(η₂)` are collinear in `γ`, giving the symmetric Vandermonde relation

`(γ₂ - γ₀)·Q(η₁) + (γ₀ - γ₁)·Q(η₂) = (γ₂ - γ₁)·Q(η₀)`.

This is the **sum** relation underlying the Case-II descent. Combined with the σ-stable
cross identities `Q(ηᵢ) = (yᵢ/xᵢ)³⁷·uᵢ⁻¹·Q(η₀)` it produces a 3-term `C₁ξ³⁷ + C₂η³⁷ = C₃ζ³⁷`
descent equation whose coefficients `γᵢ - γⱼ` carry `(ζ-1)`-content
(`caseII_K_trace_diff_factors`), reproducing the `(ζ-1)^m`-power drop of Washington 9.4. -/

/-- **Symmetric Vandermonde relation among the σ-stable pair products.** With
`γ_η = η + η^36` the real K-trace and `Q(η) = caseII_data_pair_realGenerator_K D η`,
`(γ₂ - γ₀)·Q(η₁) + (γ₀ - γ₁)·Q(η₂) = (γ₂ - γ₁)·Q(η₀)`. The affine-in-`γ` structure makes
this a pure `ring` identity once each `Q` is expanded. -/
theorem caseII_symmetric_vandermonde {m : ℕ} (D : RealCaseIIData37 K m)
    (η₀ η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    (((η₂ : 𝓞 K) + (η₂ : 𝓞 K) ^ 36) - ((η₀ : 𝓞 K) + (η₀ : 𝓞 K) ^ 36)) *
          caseII_data_pair_realGenerator_K D η₁ +
        (((η₀ : 𝓞 K) + (η₀ : 𝓞 K) ^ 36) - ((η₁ : 𝓞 K) + (η₁ : 𝓞 K) ^ 36)) *
          caseII_data_pair_realGenerator_K D η₂ =
      (((η₂ : 𝓞 K) + (η₂ : 𝓞 K) ^ 36) - ((η₁ : 𝓞 K) + (η₁ : 𝓞 K) ^ 36)) *
        caseII_data_pair_realGenerator_K D η₀ := by
  rw [caseII_data_pair_realGenerator_K_eq, caseII_data_pair_realGenerator_K_eq,
    caseII_data_pair_realGenerator_K_eq,
    caseII_pair_product_symmetric_expansion D η₀,
    caseII_pair_product_symmetric_expansion D η₁,
    caseII_pair_product_symmetric_expansion D η₂]
  ring

/-- **The σ-stable Case-II descent equation.** Combining the symmetric Vandermonde relation with
the per-root σ-stable cross identities `Xᵢ³⁷·Q(ηᵢ)·Uᵢ = Yᵢ³⁷·Q(η₀)` (where `Xᵢ = algebraMap
Gᵢ.xPlus` etc.) at the adjacent test roots `η₁ = D.etaOne`, `η₂ = D.etaTwo` (anchor
`η₀ = D.etaZero`) yields the 3-term descent equation

`(γ₂-γ₀)·U₂·(Y₁X₂)³⁷ + (γ₀-γ₁)·U₁·(Y₂X₁)³⁷ = (γ₂-γ₁)·U₁·U₂·(X₁X₂)³⁷`

in `𝓞 K`, with `γᵢ = ηᵢ + ηᵢ³⁶` the real K-traces. The coefficient differences `γᵢ - γⱼ` carry
`(ζ-1)`-content (`caseII_K_trace_diff_factors`), the descent measure. This is the Washington 9.4
Case-II descent equation, derived from the σ-stable pair-product producer. Proof: multiply the
target by `Q(η₀) ≠ 0` and `linear_combination` the Vandermonde and two cross identities. -/
theorem caseII_descent_equation {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) -
            ((D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (G₁.yPlus * G₂.xPlus)) ^ 37 +
        (((D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36) -
            ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (G₂.yPlus * G₁.xPlus)) ^ 37 =
      (((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) -
          ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₁.xPlus * G₂.xPlus)) ^ 37 := by
  obtain ⟨u₁, h₁⟩ := caseII_sigma_pair_pow37_K_anchor_sq D hp D.etaOne G₁
  obtain ⟨u₂, h₂⟩ := caseII_sigma_pair_pow37_K_anchor_sq D hp D.etaTwo G₂
  refine ⟨u₁, u₂, ?_⟩
  simp only [map_mul]
  set X₁ := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G₁.xPlus with hX₁
  set Y₁ := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G₁.yPlus with hY₁
  set X₂ := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G₂.xPlus with hX₂
  set Y₂ := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) G₂.yPlus with hY₂
  set U₁ := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _) with hU₁
  set U₂ := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _) with hU₂
  set Q₀ := caseII_data_pair_realGenerator_K D D.etaZero with hQ₀
  set Q₁ := caseII_data_pair_realGenerator_K D D.etaOne with hQ₁
  set Q₂ := caseII_data_pair_realGenerator_K D D.etaTwo with hQ₂
  have hsq : (D.x + D.y) ^ 2 = Q₀ := (caseII_data_pair_realGenerator_K_at_etaZero_eq_sq D hp).symm
  rw [hsq] at h₁ h₂
  have hV := caseII_symmetric_vandermonde D D.etaZero D.etaOne D.etaTwo
  have hQ₀_ne : Q₀ ≠ 0 := by
    rw [hQ₀, caseII_data_pair_realGenerator_K_at_etaZero_eq_sq D hp]
    exact caseII_data_x_add_y_sq_ne_zero D hp
  apply mul_right_cancel₀ hQ₀_ne
  set γ₀ := (D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36 with hγ₀
  set γ₁ := (D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36 with hγ₁
  set γ₂ := (D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36 with hγ₂
  linear_combination
    (-(γ₂ - γ₀) * U₂ * X₂ ^ 37) * h₁ + (-(γ₀ - γ₁) * U₁ * X₁ ^ 37) * h₂ +
      U₁ * U₂ * X₁ ^ 37 * X₂ ^ 37 * hV

/-- **K-trace minus 2 factors as `η⁻¹·(η-1)²`.** For a 37th root `η`,
`(η + η³⁶) - 2 = η³⁶·(η - 1)²` (since `η⁻¹ = η³⁶` and `η³⁷ = 1`). With `D.etaZero = 1` so
`γ₀ = 2`, this gives the clean factorization of every descent coefficient `γ_η - γ₀`. -/
theorem caseII_K_trace_sub_two_eq {m : ℕ} (_D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    ((η : 𝓞 K) + (η : 𝓞 K) ^ 36) - 2 = (η : 𝓞 K) ^ 36 * ((η : 𝓞 K) - 1) ^ 2 := by
  have hη : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have h38 : (η : 𝓞 K) ^ 38 = (η : 𝓞 K) := by
    rw [show (38 : ℕ) = 37 + 1 from rfl, pow_add, hη, one_mul, pow_one]
  have hexp : (η : 𝓞 K) ^ 36 * ((η : 𝓞 K) - 1) ^ 2 =
      (η : 𝓞 K) ^ 38 - 2 * (η : 𝓞 K) ^ 37 + (η : 𝓞 K) ^ 36 := by ring
  rw [hexp, h38, hη]
  ring

/-- **`Associated (η - 1) (ζ - 1)`** for a 37th root `η ≠ 1`. Instance of mathlib's
`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime` (associate of `ζ-1` with any
difference `η₁ - η₂` of distinct 37th roots), taking `η₁ = η`, `η₂ = 1`. -/
theorem caseII_root_sub_one_associated {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη_ne : (η : 𝓞 K) ≠ 1) :
    Associated ((η : 𝓞 K) - 1) (D.hζ.toInteger - 1) := by
  have h1mem : (1 : 𝓞 K) ∈ nthRootsFinset 37 (1 : 𝓞 K) :=
    one_mem_nthRootsFinset (by norm_num)
  have hpair := D.hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
    (by decide : Nat.Prime 37) η.2 h1mem hη_ne
  exact hpair.symm

/-- **`Associated (γ_η - 2) ((ζ-1)²)`** for a 37th root `η ≠ 1`. From the factorization
`γ_η - 2 = η³⁶·(η-1)²` (`caseII_K_trace_sub_two_eq`) with `η³⁶` a unit and
`Associated (η-1) (ζ-1)` (`caseII_root_sub_one_associated`). Every σ-stable descent coefficient
is therefore associate to `(ζ-1)²`, so the descent equation normalises to unit coefficients. -/
theorem caseII_K_trace_sub_two_associated {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη_ne : (η : 𝓞 K) ≠ 1) :
    Associated (((η : 𝓞 K) + (η : 𝓞 K) ^ 36) - 2) ((D.hζ.toInteger - 1 : 𝓞 K) ^ 2) := by
  rw [caseII_K_trace_sub_two_eq D η]
  have hη37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have hη_unit : IsUnit ((η : 𝓞 K) ^ 36) :=
    IsUnit.of_mul_eq_one (a := (η : 𝓞 K) ^ 36) (b := (η : 𝓞 K))
      (by rw [← pow_succ]; exact hη37)
  have hη_assoc : Associated ((η : 𝓞 K) - 1) (D.hζ.toInteger - 1) :=
    caseII_root_sub_one_associated D η hη_ne
  exact (associated_unit_mul_left (((η : 𝓞 K) - 1) ^ 2) ((η : 𝓞 K) ^ 36) hη_unit).trans
    hη_assoc.pow_pow

/-- **Sharp non-anchor valuation: `(ζ-1)² ∤ (x + yη)` for `η ≠ η₀`.** Since
`span{x+yη} = 𝔪·𝔠(η)·𝔭` (`m_mul_c_mul_p`) with `𝔭 ∤ 𝔪` (`gcd(x,y)`, as `𝔭 ∤ y` by `D.hy`) and
`𝔭 ∤ 𝔠(η)` (`p_dvd_c_iff`, as `η ≠ η₀`), the `𝔭`-valuation of `x+yη` is exactly `1`. Together
with `caseII_K_zeta_sub_one_dvd_x_add_y_times_root` (`(ζ-1) ∣ x+yη`) this pins `v_𝔭(x+yη) = 1`,
hence `v_𝔭(Q(η)) = 2` for adjacent `η` — the base of the descent's `(ζ-1)`-valuation count. -/
theorem caseII_zeta_sub_one_sq_not_dvd_x_add_y_root {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero) :
    ¬ (D.hζ.toInteger - 1 : 𝓞 K) ^ 2 ∣ (D.x + D.y * (η : 𝓞 K)) := by
  intro hdvd
  have h_eq := m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have hdvd_ideal : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ 2 ∣
      gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) := by
    rw [h_eq, Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hdvd)
  have hp_ne : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ≠ 0 := p_ne_zero D.hζ
  rw [sq] at hdvd_ideal
  have hp_dvd_mc : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η :=
    (mul_dvd_mul_iff_right hp_ne).mp hdvd_ideal
  have hp_prime : Prime (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) :=
    Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime'
  rcases hp_prime.dvd_mul.mp hp_dvd_mc with hm | hc
  · -- 𝔭 ∣ 𝔪 ⟹ 𝔭 ∣ span{y} ⟹ (ζ-1) ∣ y, contradiction with D.hy.
    have h_dvd_y : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
        Ideal.span ({D.y} : Set (𝓞 K)) := hm.trans (gcd_dvd_right _ _)
    apply D.hy
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton] at h_dvd_y
  · -- 𝔭 ∣ 𝔠(η) ⟹ η = η₀, contradiction with hη.
    have hη_eq : η = zetaSubOneDvdRoot hp D.hζ D.equation D.hy :=
      (p_dvd_c_iff hp D.hζ D.equation D.hy η).mp hc
    exact hη hη_eq

end BernoulliRegular.FLT37.LehmerVandiver.CaseII

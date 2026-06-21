import BernoulliRegular.FLT37.Eichler.CaseIISection91DescendedDatum
import BernoulliRegular.FLT37.Eichler.CaseIISection91ProductHalfProof
import BernoulliRegular.FLT37.Eichler.CaseIIFreeContentDescentStep

/-!
# [FLT37-CASEII-R2] Final assembly: §9.1 factor equations into the free-content descent step

This file performs the **final assembly** of Washington's §9.1 Theorem-9.4 descent on the
**free-content** frame (`FreeContentCaseIIData37`, `CaseIIFreeContentDatum.lean`).  It wires the
already-proven §9.1 pieces into the proven capstone
`freeContentCaseIIData37_of_factorEquations` (`CaseIISection91DescendedDatum.lean`), reducing the
content-`37·(m+1)` free-content descent step to **exactly** the §9.1 *factor-equation extraction
data* (the anchor equation `x+y = η₀·Λ^e·ρ₀³⁷`, Assumption II, and the two sharp `𝔭`-valuation
invariants `hxy'`/`hdenom'`) plus the **coprimality** `IsCoprime ((x)) ((y))`.

## What is PROVEN here (real, axiom-clean Lean — no `sorry`, no `axiom`)

* `caseII_section91_factorEquations_etaOne_etaTwo` — **the two factor equations at the adjacent
  roots `η = ζ` (`= etaOne`) and `η = ζ²` (`= etaTwo`)**, in the `hfa_pos`/`hfa_neg` shape the
  capstone consumes, from the proven producer `caseII_section91_factorEquations`
  (`CaseIISection91FactorProducer.lean`, with the product half **proven** in
  `CaseIISection91ProductHalfProof.lean`).  The two roots satisfy `1 ≢ ±2 (mod 37)` (so `ηA·ηB ≠ 1`,
  `ηA ≠ ηB`), the capstone's distinctness hypotheses.

* `CaseIISection91AnchorExtractionData37` — a `def … : Prop` bundling the **genuine** remaining §9.1
  inputs over a real datum `D` with coprimality: the anchor equation
  `algebraMap(x+y) = η₀·Λ^e·ρ₀³⁷` (`η₀` real, `ρ₀ ∈ K`, `e ≥ 1`), **Assumption II**
  `η_a = u³⁷·η_b` for the two factor-equation units, integer witnesses `ω, θ, z'` for the
  conjugate-norm building blocks, the σ-fixed-unit descent witness `δ'`, the datum invariants
  (reality of `ω, θ`; `𝔭`-coprimality of `θ, z'`; `(ζ−1)³ ∣ ω+θ`; the sharp `hdenom'`), and the
  ideal fact `(z') = 𝔞₀ᵏ` (`k ≥ 1`) that makes the descended Fermat variable **anchor-supported**.

* `freeContentCaseIIData37_pContent_descend_of_anchorExtractionData` — **the content-`37·(m+1)`
  free-content descent step from the §9.1 extraction data**: feeding the two factor equations, the
  anchor equation, Assumption II, the witnesses and invariants into the capstone yields a
  `FreeContentCaseIIData37 K (4e−2)` with `D'.z = z'`; the proven anchor-support strict drop
  (`caseIIZFactorCount_strict_of_anchor_supported`) then gives `count(z') < count(z)`.  This is an
  alternative, direct discharge of the content-`37·(m+1)` step (cf.
  `freeContentCaseIIDescentStep37_of_assembly_on_p_content`), bypassing the §4 assembly residual.

## The honest residual map (soundness-first)

Three inputs are **genuinely** needed and are **not** asserted free here:

1. **Assumption II** (`η_a = u³⁷·η_b`): the Kummer–Furtwängler unit-power step.  It is *not*
   unconditionally provable; in the repo it reduces (via Washington Lemma 9.8/9.9 / Cor 8.23) to the
   carried second-order Bernoulli input `NoSecondOrderIrregularPair 37 32` (Kellner) plus the
   genuine single-index residuals.  Carried here inside `CaseIISection91AnchorExtractionData37`.

2. **Coprimality** `IsCoprime ((x)) ((y))`: true for the base producer's data
   (`gcd(a,b,c) = 1 ⟹ gcd(x,y) = 1`), but it is **not** a field of `RealCaseIIData37`/`CaseIIData37`
   (verified — the structures carry only `hy`, `hz`).  Threaded as an explicit hypothesis.

3. **The invariants** `hxy'` (`(ζ−1)³ ∣ ω+θ`) and `hdenom'` (`v_𝔭(ω+θζ³⁶) = 1`): sharp
   `𝔭`-valuation facts about the conjugate-norm building blocks, **not** derivable from the
   descended equation (`CaseIIFreeContentDatumPackaging.lean` §4).  Carried inside the extraction
   data.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), pp. 171–173,
  179–180.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The two factor equations at the adjacent roots `η = ζ`, `η = ζ²` (PROVEN) -/

/-- **[FACTOR EQUATIONS AT `ζ`, `ζ²`] The two conjugate-paired §9.1 factor equations at the adjacent
roots `etaOne = ζ` and `etaTwo = ζ²`**, in the cleared-denominator shape the capstone consumes.

For a real Case-II datum `D` and the coprimality `IsCoprime ((x)) ((y))`, the proven producer
`caseII_section91_factorEquations` (with the product half **proven**,
`caseIISection91ProductHalf37_proven`) supplies real units `η_a, η_b : Kˣ` and generators
`ρ_a, ρ_b : K` with the four factor equations
```
x + ζ·y    = (1 − ζ)   · η_a · ρ_a³⁷,     x + ζ³⁶·y    = (1 − ζ³⁶)   · η_a · (σρ_a)³⁷,
x + ζ²·y   = (1 − ζ²)  · η_b · ρ_b³⁷,     x + ζ⁷²·y    = (1 − ζ⁷²)  · η_b · (σρ_b)³⁷,
```
where `x = algebraMap D.x`, `y = algebraMap D.y`, and `σ = complexConj`.  Here `ζ³⁶ = ζ⁻¹` and
`ζ⁷² = ζ⁻²` are the integer roots `(ζ)^36`, `(ζ²)^36`.  Both `η_a, η_b` are real (`σ η = η`).

These are exactly the `hfa_pos`/`hfa_neg`/`hfb_pos`/`hfb_neg` hypotheses of the capstone
`freeContentCaseIIData37_of_factorEquations` with `ηA = ζ`, `ηB = ζ²`. -/
theorem caseII_section91_factorEquations_etaOne_etaTwo
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) ∧
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) ∧
      -- factor equations at `ηA = ζ`:
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 36) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 36)) *
          (ηa : CyclotomicField 37 ℚ) * (complexConj (CyclotomicField 37 ℚ) ρa) ^ 37) ∧
      -- factor equations at `ηB = ζ²`:
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((D.hζ.toInteger ^ 2) ^ 36) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
              ((D.hζ.toInteger ^ 2) ^ 36)) *
          (ηb : CyclotomicField 37 ℚ) * (complexConj (CyclotomicField 37 ℚ) ρb) ^ 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- The two adjacent roots `η = etaOne = ζ`, `η = etaTwo = ζ²` (both `≠ etaZero`).
  obtain ⟨ηa, ρa, hηa_real, hfa_pos, hfa_neg⟩ :=
    caseII_section91_factorEquations caseIISection91ProductHalf37_proven D D.etaOne
      D.toCaseIIData37.etaOne_ne_etaZero hcop
  obtain ⟨ηb, ρb, hηb_real, hfb_pos, hfb_neg⟩ :=
    caseII_section91_factorEquations caseIISection91ProductHalf37_proven D D.etaTwo
      D.toCaseIIData37.etaTwo_ne_etaZero hcop
  -- Identify the root coes: `etaOne = ζ`, `etaTwo = ζ²`.
  have hηOne : (D.etaOne : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger :=
    caseII_etaOne_coe_eq_zeta D hp
  have hηTwo : (D.etaTwo : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger ^ 2 := by
    rw [caseII_etaTwo_coe_eq_zeta_sq D hp, pow_two]
  refine ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, ?_, ?_, ?_, ?_⟩
  · rw [← hηOne]; exact hfa_pos
  · rw [← hηOne]; exact hfa_neg
  · rw [← hηTwo]; exact hfb_pos
  · rw [← hηTwo]; exact hfb_neg

/-! ## 2. The genuine §9.1 extraction data (the residual, `def … : Prop`)

The capstone `freeContentCaseIIData37_of_factorEquations` needs, beyond the proven factor equations,
three genuine §9.1 inputs that the descent **construction** supplies but that are **not** derivable
from the equation/datum:

* the **anchor equation** `algebraMap(x+y) = η₀·Λ^e·ρ₀³⁷` (`η₀` real, `ρ₀ ∈ K`, `e ≥ 1`) — the
  `B₀` analysis directly on `x+y`;
* **Assumption II** `η_a = u³⁷·η_b` for the two factor-equation units — the Kummer–Furtwängler
  unit-power step (reduces to the carried Kellner input + the genuine single-index residual);
* integer witnesses `ω, θ, z'` for the conjugate-norm building blocks, the σ-fixed-unit descent
  witness `δ'`, the two sharp `𝔭`-valuation invariants `hxy'`/`hdenom'`, and the ideal fact
  `(z') = 𝔞₀ᵏ` (`k ≥ 1`) making the descended Fermat variable anchor-supported.

We bundle exactly these — **keyed to the factor-equation outputs** `(η_a, η_b, ρ_a, ρ_b)` — as the
residual `CaseIISection91AnchorExtractionData37`.  It is a genuine implication (not vacuous): the
factor-equation outputs exist (`caseII_section91_factorEquations_etaOne_etaTwo`), and its conclusion
is the §9.1 construction's output. -/

/-- **[FLT37-CASEII-§9.1-EXTRACTION-DATA] The genuine §9.1 factor-equation extraction data** (a
`def … : Prop`, **not** an axiom).

For every real Case-II datum `D` with coprime Fermat variables, and **every** choice of the proven
factor-equation outputs `η_a, η_b : Kˣ` (real) and `ρ_a, ρ_b : K` at the roots `ζ`, `ζ²` (i.e.
satisfying the four cleared-denominator factor equations), the §9.1 descent construction supplies:

* an **anchor exponent** `e ≥ 1`, a **real** anchor unit `η₀ : Kˣ`, and an anchor generator
  `ρ₀ : K` with `algebraMap(x+y) = η₀·Λ^e·ρ₀³⁷` (`Λ = (1−ζ)(1−ζ³⁶)`);
* **Assumption II** `η_a = u³⁷·η_b` for a unit `u : Kˣ`;
* integer witnesses `ω, θ, z' : 𝓞 K` for `u²ρ_aσρ_a`, `−ρ_bσρ_b`, `ρ₀²`;
* a σ-fixed-unit descent witness `δ'` (the descended σ-fixed unit lands in `(𝓞 K)ˣ`);
* the datum invariants: reality of `ω, θ`; `𝔭`-coprimality of `θ, z'`; `(ζ−1)³ ∣ ω+θ`; the sharp
  `v_𝔭(ω+θζ³⁶) = 1`; and the anchor-support ideal fact `(z') = 𝔞₀ᵏ` (`k ≥ 1`).

This is the **single** remaining content of Washington §9.1/Theorem 9.4 on the free-content frame:
the factor equations, the conjugate-norm reassembly algebra, the `Λ → (ζ−1)`-content repackaging,
the datum closure, the terminal first-layer contradiction, and the well-founded factor-count descent
are all proven elsewhere; **this** packages the construction's anchor/Assumption-II/invariant
outputs. -/
def CaseIISection91AnchorExtractionData37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) →
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) →
      ∃ (e k : ℕ) (η0 u : (CyclotomicField 37 ℚ)ˣ) (ρ0 : CyclotomicField 37 ℚ)
        (ω θ z' : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        1 ≤ e ∧ 1 ≤ k ∧
        -- anchor equation (in `zeta_spec`-terms, the capstone's `Λ`):
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
          (η0 : CyclotomicField 37 ℚ) *
            (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
              ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e * ρ0 ^ 37 ∧
        -- Assumption II:
        (ηa : (CyclotomicField 37 ℚ)ˣ) = u ^ 37 * ηb ∧
        complexConj (CyclotomicField 37 ℚ) (η0 : CyclotomicField 37 ℚ) =
          (η0 : CyclotomicField 37 ℚ) ∧
        -- integer witnesses:
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (u : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) z' = ρ0 ^ 2 ∧
        -- σ-fixed-unit descent witness (`zeta_spec`-terms):
        (∀ δ : (CyclotomicField 37 ℚ)ˣ,
          complexConj (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ) =
              (δ : CyclotomicField 37 ℚ) →
          ((u : CyclotomicField 37 ℚ) ^ 2 *
                (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
              (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
            (δ : CyclotomicField 37 ℚ) *
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                  (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) *
              (ρ0 ^ 2) ^ 37 →
          (δ : CyclotomicField 37 ℚ) =
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _)) ∧
        -- datum invariants (`zeta_spec`-terms, the capstone's `𝔭`):
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ ∧
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 3 ∣ ω + θ ∧
        (∃ c : 𝓞 (CyclotomicField 37 ℚ),
          ω + θ * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 =
              ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) * c ∧
            ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣ c) ∧
        -- anchor-support of the descended Fermat variable (`D.hζ`-terms, the drop's anchor):
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k

/-! ## 3. Bridging `D.hζ` and `zeta_spec`: associatedness of the two `(ζ−1)` uniformizers -/

/-- **`Associated (D.hζ.toInteger − 1) ((zeta_spec).toInteger − 1)`** for a real Case-II datum `D`.

Both `D.hζ.toInteger` and `(zeta_spec 37 ℚ K).toInteger` are primitive `37`-th roots of unity, so
their `−1` translates are associated (`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`).
Used to
bridge the `D.hζ`-based anchor-support `(z') = 𝔞₀ᵏ` (`𝔭`-coprime) to the `zeta_spec`-based
`¬ (zeta_spec − 1) ∣ z'` the capstone consumes. -/
theorem caseII_section91_zeta_sub_one_associated_zeta_spec
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    Associated (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Base the pairwise lemma at `ζ = zeta_spec`, with `η₁ = D.hζ.toInteger`, `η₂ = 1`:
  -- `Associated (zeta_spec − 1) (D.hζ.toInteger − 1)`; take `.symm`.
  have hmem_dζ : D.hζ.toInteger ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
  have hmem_one : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    one_mem_nthRootsFinset (by norm_num)
  have hne : D.hζ.toInteger ≠ (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hpair := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot
    |>.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hmem_dζ hmem_one hne
  -- `hpair : Associated (zeta_spec − 1) (D.hζ.toInteger − 1)`; `.symm` is the goal.
  simpa using hpair.symm

/-! ## 4. The content-`37·(m+1)` free-content descent step from the §9.1 extraction data (PROVEN) -/

set_option maxRecDepth 4000 in
/-- **[FREE-CONTENT DESCENT STEP, content `37·(m+1)`, from the §9.1 extraction data]**

For a free-content datum `D` at content `37·(m+1)` in the non-terminal regime (corrected radical at
`η = ζ` not a unit), with coprime Fermat variables `IsCoprime ((x)) ((y))`, the **§9.1 extraction
data** (`CaseIISection91AnchorExtractionData37`) yields a free-content datum `D'` with strictly
fewer distinct prime factors of its Fermat variable:
`caseIIFreeFactorCount D' < caseIIFreeFactorCount D`.

Proof: promote `D` to `RealCaseIIData37 m`; prove the two factor equations at `ζ`, `ζ²`
(`caseII_section91_factorEquations_etaOne_etaTwo`, from the proven product half); feed them to the
§9.1 extraction data to obtain the anchor equation, Assumption II, integer witnesses, the
σ-fixed-unit descent witness, the two invariants, and the anchor-support `(z') = 𝔞₀ᵏ`; feed
everything to the **proven** capstone `freeContentCaseIIData37_of_factorEquations`, getting a
`FreeContentCaseIIData37` `D'` with `D'.z = z'`; the **proven** anchor-support strict drop
(`caseIIZFactorCount_strict_of_anchor_supported`, after bridging `z'`'s `𝔭`-coprimality via
`caseII_anchorSupported_of_span_eq_anchorPow`) gives `count(z') < count(z)`. -/
theorem freeContentCaseIIData37_pContent_descend_of_anchorExtractionData
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_data : CaseIISection91AnchorExtractionData37)
    {m : ℕ} (D : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) (37 * (m + 1)))
    (hcop : IsCoprime
      (Ideal.span ({(freeContentCaseIIData37_toReal D).x} :
        Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({(freeContentCaseIIData37_toReal D).y} :
        Set (𝓞 (CyclotomicField 37 ℚ)))))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 (CyclotomicField 37 ℚ) n'),
      caseIIFreeFactorCount D' < caseIIFreeFactorCount D := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  set Dr := freeContentCaseIIData37_toReal D with hDr
  -- Transfer the non-terminal hypothesis to the real datum `Dr`.
  have hnonterm' : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical Dr Dr.etaOne (caseII_correctionUnit Dr.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← caseIIFree_correctedRadical_eq_real D]; exact hnonterm
  -- The proven factor equations at `ζ`, `ζ²`.
  obtain ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, hfa_pos, hfa_neg, hfb_pos, hfb_neg⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo Dr hcop
  -- The §9.1 extraction data: anchor + Assumption II + witnesses + invariants + anchor-support.
  obtain ⟨e, k, η0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
      hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span⟩ :=
    h_data Dr hcop ηa ηb ρa ρb hηa_real hηb_real hfa_pos hfb_pos
  -- `¬ (zeta_spec − 1) ∣ z'`: from `(z') = 𝔞₀ᵏ` (`𝔭`-coprime, `D.hζ`-terms) + associatedness.
  have hz'cop_dζ : ¬ (Dr.hζ.toInteger - 1) ∣ z' := by
    have hnot : ¬ Ideal.span ({(Dr.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [hz'_span]
      intro hdvd
      exact not_p_div_a_zero hp Dr.hζ Dr.equation Dr.hy Dr.hz
        ((Ideal.prime_span_singleton_iff.mpr Dr.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  have hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z' := by
    have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec Dr
    intro hdvd
    exact hz'cop_dζ (hassoc.dvd.trans hdvd)
  -- The capstone: from the factor equations + anchor + Assumption II + witnesses + invariants,
  -- produce a `FreeContentCaseIIData37` `D'` with `D'.z = z'`.
  -- The capstone's `ηA = ζ`, `ηB = ζ²`; `Λa, Λb, Λ` are the `Kˣ` of the (nonzero) `(1−η)(1−η³⁶)`.
  set ηA : 𝓞 (CyclotomicField 37 ℚ) := Dr.hζ.toInteger with hηA
  set ηB : 𝓞 (CyclotomicField 37 ℚ) := Dr.hζ.toInteger ^ 2 with hηB
  -- `ηA^37 = 1`, `ηB^37 = 1`.
  have hA37 : ηA ^ 37 = 1 := by
    rw [hηA]; exact Dr.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hB37 : ηB ^ 37 = 1 := by
    rw [hηB, ← pow_mul, show 2 * 37 = 37 * 2 from by norm_num, pow_mul, hA37, one_pow]
  -- `ηA ≠ 1`, `ηB ≠ 1`, `ηA ≠ ηB`, `ηA·ηB ≠ 1`.
  have hA1 : ηA ≠ 1 := Dr.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hB1 : ηB ≠ 1 := by
    rw [hηB]
    exact Dr.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
  have hAB : ηA ≠ ηB := by
    rw [hηA, hηB, pow_two]
    intro h
    -- `ζ = ζ·ζ ⟹ ζ·(ζ−1) = 0 ⟹ ζ = 0 ∨ ζ = 1`, both false.
    have hz0 : Dr.hζ.toInteger * (Dr.hζ.toInteger - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz0 with h0 | h1
    · exact Dr.hζ.toInteger_isPrimitiveRoot.ne_zero (by decide : 37 ≠ 0) h0
    · exact hA1 (by rw [hηA]; linear_combination h1)
  have hABp : ηA * ηB ≠ 1 := by
    rw [hηA, hηB, show Dr.hζ.toInteger * Dr.hζ.toInteger ^ 2 = Dr.hζ.toInteger ^ 3 from by ring]
    exact Dr.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 3 < 37)
  -- The three `Λ`-units.
  have hΛne : ∀ (η : 𝓞 (CyclotomicField 37 ℚ)), η ^ 37 = 1 → η ≠ 1 →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((1 - η) * (1 - η ^ 36)) ≠ 0 := by
    intro η hη37 hη1
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    refine mul_ne_zero (fun h0 ↦ hη1 (by linear_combination -h0)) (fun h0 ↦ ?_)
    -- `1 - η³⁶ = 0 ⟹ η³⁶ = 1 ⟹ η = η³⁷·(η³⁶)⁻¹ = 1·... `; use `η^36 = 1` and `η^37 = 1`.
    have h36 : η ^ 36 = 1 := by linear_combination -h0
    have : η = 1 := by
      have hsucc : η ^ 37 = η ^ 36 * η := by rw [pow_succ]
      rw [hη37, h36, one_mul] at hsucc; exact hsucc.symm
    exact hη1 this
  have hΛspec_ne := hΛne (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one)
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37))
  set Λa : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ (hΛne ηA hA37 hA1) with hΛa_def
  set Λb : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ (hΛne ηB hB37 hB1) with hΛb_def
  set Λ : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ hΛspec_ne with hΛ_def
  have hΛa_val : (Λa : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ) ((1 - ηA) * (1 - ηA ^ 36)) := rfl
  have hΛb_val : (Λb : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ) ((1 - ηB) * (1 - ηB ^ 36)) := rfl
  have hΛ_val : (Λ : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ)
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) := rfl
  -- The anchor equation in the capstone's `x + y` shape.
  have hanchor' : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.x +
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.y =
      (η0 : CyclotomicField 37 ℚ) * (Λ : CyclotomicField 37 ℚ) ^ e * ρ0 ^ 37 := by
    rw [hΛ_val, ← map_add]; exact hanchor
  -- Feed everything to the proven capstone.
  obtain ⟨n', D', hD'z⟩ :=
    freeContentCaseIIData37_of_factorEquations (K := CyclotomicField 37 ℚ)
      (x := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.x)
      (y := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.y)
      (ρa := ρa) (ρb := ρb) (ρ0 := ρ0) (ηa := ηa) (ηb := ηb) (η0 := η0) (u := u)
      (ηA := ηA) (ηB := ηB) (Λa := Λa) (Λb := Λb) (Λ := Λ) (e := e)
      he hA37 hB37 hA1 hB1 hAB hABp hΛa_val hΛb_val hΛ_val
      hfa_pos hfa_neg hfb_pos hfb_neg hanchor' hII hη0real hηb_real
      hω hθ hz' hδ' hω_real hθ_real hθ_cop hz'_cop hxy' hdenom'
  -- Now `D' : FreeContentCaseIIData37 n'` with `D'.z = z'`.  The factor-count strict drop.
  refine ⟨n', D', ?_⟩
  -- `caseIIFreeFactorCount D' = count(z')`; `caseIIFreeFactorCount D = caseIIZFactorCount Dr`.
  rw [caseIIFreeFactorCount, hD'z, caseIIFreeFactorCount_toReal D]
  -- `support(z') ⊆ support(𝔞₀)` from `(z') = 𝔞₀ᵏ`; anchor-support strict drop.
  have hsupp := caseII_anchorSupported_of_span_eq_anchorPow Dr hk hz'_span
  exact caseIIZFactorCount_strict_of_anchor_supported Dr hp hnonterm' hsupp

/-! ## 5. Non-vacuity of the extraction data, and the honest residual map

The proven `freeContentCaseIIData37_pContent_descend_of_anchorExtractionData` discharges the
free-content descent step **at the contents `37·(m+1)`** (reachable by the promotion
`freeContentCaseIIData37_toReal`, where the flt-regular root-ideal factor-equation extraction runs),
**from** the §9.1 extraction data `CaseIISection91AnchorExtractionData37` **and** the coprimality
`IsCoprime ((x)) ((y))` of the promoted Fermat variables — both threaded as genuine inputs, never as
false universals.

### Why the inputs are genuine (soundness verdict)

* **Coprimality is not free.**  It is *not* a datum invariant (verified: `FreeContentCaseIIData37` /
  `RealCaseIIData37` carry only `hy`, `hz`), and the universal "every free-content datum has coprime
  `x, y`" is **provably false**: scaling a base datum `(x₀, y₀, z₀)` by a rational prime `p ≠ 37`
  gives a valid `FreeContentCaseIIData37` with `gcd(x, y) ⊇ (p) ≠ 1` (`p` is coprime to the ramified
  `𝔭 = (ζ−1)`, so `hy`, `hz` survive).  Hence coprimality is correctly threaded as a *hypothesis* of
  the descent theorem, not asserted.

* **Assumption II is not free.**  `η_a = u³⁷·η_b` is the Kummer–Furtwängler unit-power step; in the
  repo it reduces (Washington Lemma 9.8/9.9, Cor 8.23) to the carried second-order Bernoulli input
  `NoSecondOrderIrregularPair 37 32` (Kellner) plus the genuine single-index residuals — not
  unconditional.  Carried inside `CaseIISection91AnchorExtractionData37`.

* **The invariants `hxy'`/`hdenom'` are not free.**  Sharp `𝔭`-valuation facts about the
  conjugate-norm building blocks, not derivable from the descended equation
  (`CaseIIFreeContentDatumPackaging.lean` §4).  Carried inside the extraction data.

* **The non-`p`-content regime is open.**  One descent step lands at content `4e−2 ≢ 0 (mod 37)`,
  where the root-ideal extraction does not apply to a free-content datum.  This is the residual the
  free-content frame was built to address; it is **not** closed here.

The remaining `def … : Prop` certifies the extraction data's antecedent is inhabited (the factor
equations exist), so the residual is a *genuine implication*, not vacuous. -/

/-- **Non-vacuity of `CaseIISection91AnchorExtractionData37` (antecedent inhabited).**  For a real
Case-II datum `D` with coprime Fermat variables, the factor-equation outputs the extraction data is
keyed to **exist** (`caseII_section91_factorEquations_etaOne_etaTwo`, from the proven product half).
So the extraction data consumes inhabited input — it is a genuine implication, not vacuously true
for the wrong reason. -/
theorem caseIISection91AnchorExtractionData37_antecedent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) ∧
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) := by
  obtain ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, hfa_pos, _, hfb_pos, _⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo D hcop
  exact ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, hfa_pos, hfb_pos⟩

end BernoulliRegular.FLT37.Eichler

end

end

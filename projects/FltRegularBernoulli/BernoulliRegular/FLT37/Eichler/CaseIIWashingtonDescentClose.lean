import BernoulliRegular.FLT37.Eichler.CaseIIAnchorRealRho0
import BernoulliRegular.FLT37.Eichler.CaseIISection91ExtractionProducer
import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonLemma96SharpInvariants

/-!
# [FLT37-CASEII-R2-L5] Closing Washington's §9.1 second-case descent: L1 + L2 wired in

This is the **R2 milestone** (`.mathlib-quality/tickets-flt37-r2.md`, `T-R2-L5`): close FLT37
Case-II by composing the now-proven §9.1 leaves into the descent step + the FLT37 endpoint.

## What the two proven leaves give (and what they replace)

The prior endpoints (`CaseIIModuloKellner.lean`,
`fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction`) carried the **entire** §9.1
geometric construction inside one giant residual `CaseIISection91DvdZGenuineUnitExtractionData37` —
including the **anchor equation** `x+y = η₀·Λ^e·ρ₀³⁷` and the four **factor equations**
`x+ζᵃy = (1−ζᵃ)·η_a·ρ_a³⁷`.  Those two pieces are now **proven theorems**:

* **L1 `caseII_anchor_real_rho0_impl`** (`CaseIIAnchorRealRho0.lean`): the real anchor
  `x+y = algebraMap(u₀)·Λ^e·ρ₀³⁷` with `ρ₀ : 𝓞 K` a **real** generator of the `𝔭`-free anchor
  `B₀ = aEtaZeroDvdPPow` (`(ρ₀) = B₀`, via the Vandiver `[B₀]² = 1 ∧ [B₀]³⁷ = 1` argument using
  the proven `37 ∤ h⁺`).  This is a **genuine-integral-unit** anchor (`η₀ = algebraMap u₀`,
  `u₀ : (𝓞 K)ˣ`) — exactly the form `CaseIISection91DvdZGenuineUnitExtractionData37` wants.

* **L2 `caseII_section91_factorEquations_etaOne_etaTwo`** (`CaseIIFreeContentAssembly.lean`): the
  conjugate-paired factor equations at the two adjacent roots `ζ`, `ζ²`, with **real** factor units
  `η_a, η_b` (proven via the proven product half `caseIISection91ProductHalf37_proven`).

So `T-R2-L5` discharges L1 (the anchor, with its genuine-integral-unit form **and** its
anchor-support `(ρ₀) = B₀`, hence `(ρ₀²) = B₀²`, `k = 2`) and L2 (the factor-equation production)
from the carried residual, leaving the **strictly smaller** residual
`CaseIIWashingtonSection91Witnesses37`: only the integer witnesses `ω, θ` for the conjugate-norm
building blocks `u²ρ_aσρ_a`, `−ρ_bσρ_b`, **Assumption II** `η_a = u³⁷·η_b`, the σ-fixed-unit witness
`δ'`, the two sharp `𝔭`-valuation invariants `hxy'`/`hdenom'`, and the Lemma-9.6/9.7 `ℓ`-propagation
`ω, θ ∉ 𝔩`, `z' ∈ 𝔩`.

## The reduction and the endpoint (PROVEN)

* `caseIISection91DvdZGenuineUnitExtractionData37_of_washingtonWitnesses` — **the reduction**: from
  the minimal witness residual `CaseIIWashingtonSection91Witnesses37`, produce the full
  `CaseIISection91DvdZGenuineUnitExtractionData37`, with the anchor (L1) supplied internally and
  `z' = ρ₀²` (integer, from L1's integer `ρ₀`) with anchor-support `(z') = B₀²` (L1's `(ρ₀) = B₀`).

* `caseII_washington_descent_step` — **the descent-step producer**: for a non-terminal real
  `ℓ ∣ z`-datum with coprime Fermat variables, the witness residual + the proven §9.1 reassembly
  yield a free-content datum with **strictly fewer** distinct prime factors of its Fermat variable.

* `fermatLastTheoremFor_thirtyseven_of_washingtonDescent` — **the FLT37 endpoint**: from the witness
  residual, the per-datum coprimality, Washington Lemma 9.6, and the carried Kellner input.  Routes
  through the proven `fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction`: the
  well-founded factor-count descent **inside `p`-content** (the non-`p`-content gap never arising),
  the terminal first-layer contradiction, Case I (Eichler), `37 ∤ h⁺` (Vandiver for `37`), and the
  `ℓ ∣ z` at the rational seed (`furtwangler_37_149`) are all proven and supplied internally.

## On Washington's Assumption II `η_a = u³⁷·η_b`

Assumption II as the §9.1 descent uses it is the *factor-unit* power `η_a = u³⁷·η_b` (the unit ratio
of the two factor-equation units at the adjacent roots `ζ`, `ζ²` is a `37`-th power of a unit,
Washington Theorem 9.4).  This is the §9.1-frame analogue of the repo's linear-frame
`WashingtonCaseIIExactQuotientUnitPower37Source` (`ε₁/ε₂ = ε'³⁷`, the σ-pair-product descent unit);
both are the same Kummer–Furtwängler content, but in different descent frames, and identifying
them is itself §9.1 descent-unit content.  We therefore carry Assumption II in its **§9.1 form**
inside the witness residual (keyed to the factor-equation outputs), the form this descent consumes.

## Soundness (B2-checked)

* L1 (anchor) and L2 (factor equations) are **proven** and consumed; they are no longer carried.
  `(ρ₀) = B₀` is the **proven** principality of the `𝔭`-free anchor (the Vandiver
  `caseII_anchor_B0_isPrincipal`), so `z' = ρ₀²` with `(z') = B₀²` is sound — **not** the obstructed
  `ρ₀σρ₀` mismatch (that obstruction was the unproven claim "`B₀` not principal", refuted by L1).
* Assumption II `η_a = u³⁷·η_b`, the integer witnesses, the sharp invariants, the `ℓ`-propagation,
  per-datum coprimality, and Lemma 9.6 are **carried** (the genuine remaining §9.1/Furtwängler
  content); the **universal** coprimality is provably false, so it is threaded, never asserted.

It imports only and does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), pp. 169–173;
  Lemma 9.6 (p. 179), Lemma 9.7, Lemma 9.8 (p. 180).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

open scoped Classical in
/-- **[FLT37-CASEII-§9.1-WITNESS-RESIDUAL] The §9.1 witness data, anchor + factor eqns discharged**
(a `def … : Prop`, **not** an axiom).

For a real `ℓ ∣ z` datum `D`, the per-datum coprimality, **and** the proven L1 anchor data
(`e ≥ 1`, `ρ₀ : 𝓞 K` with `(ρ₀) = B₀`, `u₀ : (𝓞 K)ˣ` real, and the anchor equation
`x+y = algebraMap(u₀)·Λ^e·ρ₀³⁷`), and **every** choice of the proven L2 factor-equation outputs
`η_a, η_b : Kˣ` (real) and `ρ_a, ρ_b : K` at the roots `ζ`, `ζ²`, the §9.1 construction supplies:

* **Assumption II** `η_a = u³⁷·η_b` for a unit `u : Kˣ`;
* integer witnesses `ω, θ : 𝓞 K` for `u²ρ_aσρ_a`, `−ρ_bσρ_b`;
* a σ-fixed-unit descent witness `δ'` (the descended σ-fixed field unit lands in `(𝓞 K)ˣ`);
* the invariants: reality of `ω, θ`; `𝔭`-coprimality of `θ`; `(ζ−1)³ ∣ ω+θ`; the sharp
  `v_𝔭(ω+θζ³⁶) = 1`; and the Lemma-9.6/9.7 membership `ω, θ ∉ 𝔩`, `ρ₀² ∈ 𝔩`.

Compared to `CaseIISection91DvdZGenuineUnitExtractionData37`, the anchor equation, the
genuine-integral-unit anchor, `ρ₀`, the integer descended variable `z' = ρ₀²`, its
`𝔭`-coprimality, and the anchor-support `(z') = B₀^k` are **dropped** — they are the proven L1
output (supplied internally by the reduction below). -/
def CaseIIWashingtonSection91Witnesses37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 →
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
      ∃ (u : (CyclotomicField 37 ℚ)ˣ)
        (ω θ : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        (ηa : (CyclotomicField 37 ℚ)ˣ) = u ^ 37 * ηb ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (u : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
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
              ((algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0) ^ 2) ^ 37 →
          (δ : CyclotomicField 37 ℚ) =
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _)) ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ ∧
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 3 ∣ ω + θ ∧
        (∃ c : 𝓞 (CyclotomicField 37 ℚ),
          ω + θ * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 =
              ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) * c ∧
            ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣ c) ∧
        ρ0 ^ 2 ∈ lv149 ∧ ω ∉ lv149 ∧ θ ∉ lv149

/-- **[L1 — genuine integral unit] The real anchor with the integral anchor unit `u₀` exposed.**

For a real Case-II datum `D` over `CyclotomicField 37 ℚ` with coprime Fermat variables, there are
`e ≥ 1`, an **integral** unit `u₀ : (𝓞 K)ˣ` with `algebraMap u₀` **real**, and a **real** generator
`ρ₀ : 𝓞 K` of the `𝔭`-free anchor `B₀ = aEtaZeroDvdPPow` (`(ρ₀) = B₀`), with the anchor
equation `algebraMap(x+y) = algebraMap(u₀)·Λ^e·algebraMap(ρ₀)³⁷`.

This is the integral-unit form L1 actually produces (`caseII_anchor_real_rho0_of_VC` sets the anchor
unit to `Units.map (algebraMap) u⁻¹`): we recover `u₀ = u⁻¹` from the principal-ideal equality
`span(x+y) = span(Λ^e·ρ₀³⁷)`. -/
theorem caseII_anchor_real_rho0_genuineUnit
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ρ0 = ρ0 ∧
      Ideal.span ({ρ0} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (u0 : 𝓞 _) = (u0 : 𝓞 _) ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ
  have hp : (37 : ℕ) ≠ 2 := by decide
  set σ := NumberField.IsCMField.ringOfIntegersComplexConj K with hσ_def
  set 𝔞₀ := aEtaZeroDvdPPow hp D.hζ D.equation D.hy with h𝔞₀_def
  set Λi : 𝓞 K := (1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36)
    with hΛi_def
  have h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr Sinnott.flt37_not_dvd_hPlus
  obtain ⟨ρ0, hρ0_real, hρ0_span⟩ := caseII_anchor_B0_real_generator D hp h_VC hcop
  obtain ⟨k, hk⟩ := realCaseIIData37_odd_m D
  set e : ℕ := 37 * k + 19 with he_def
  have h2e : 37 * m + 1 = 2 * e := by rw [hk, he_def]; ring
  set 𝔭 : Ideal (𝓞 K) := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭_def
  have hcube : Ideal.span ({D.x + D.y} : Set (𝓞 K)) = 𝔭 ^ (37 * m + 1) * 𝔞₀ ^ 37 :=
    caseII_span_x_add_y_eq_anchorCube D hp hcop
  have hΛspan : Ideal.span ({Λi} : Set (𝓞 K)) = 𝔭 ^ 2 :=
    caseII_span_lambda_eq_p_sq D.hζ (zeta_spec 37 ℚ K)
  have hp_pow : 𝔭 ^ (37 * m + 1) = Ideal.span ({Λi ^ e} : Set (𝓞 K)) := by
    rw [← Ideal.span_singleton_pow, hΛspan, ← pow_mul, h2e]
  have hρ0_pow : 𝔞₀ ^ 37 = Ideal.span ({ρ0 ^ 37} : Set (𝓞 K)) := by
    rw [h𝔞₀_def, ← hρ0_span, Ideal.span_singleton_pow]
  have hspan_eq : Ideal.span ({D.x + D.y} : Set (𝓞 K)) =
      Ideal.span ({Λi ^ e * ρ0 ^ 37} : Set (𝓞 K)) := by
    rw [hcube, hp_pow, hρ0_pow, Ideal.span_singleton_mul_span_singleton]
  obtain ⟨u, hu_eq⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan_eq
  have hxy_int : D.x + D.y = (u⁻¹ : (𝓞 K)ˣ) * (Λi ^ e * ρ0 ^ 37) := by
    have h1 : (D.x + D.y) * (u : 𝓞 K) = Λi ^ e * ρ0 ^ 37 := hu_eq
    have h2 : D.x + D.y = (Λi ^ e * ρ0 ^ 37) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
      rw [← h1, mul_assoc, Units.mul_inv, mul_one]
    rw [h2, mul_comm]
  have hΛi_ne : Λi ≠ 0 := by
    rw [hΛi_def]
    refine mul_ne_zero ?_ ?_
    · have hne : (zeta_spec 37 ℚ K).toInteger ≠ 1 :=
        (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
      exact fun h => hne (by linear_combination -h)
    · have hne : (zeta_spec 37 ℚ K).toInteger ^ 36 ≠ 1 := by
        intro h
        have h37 : (zeta_spec 37 ℚ K).toInteger ^ 37 = 1 :=
          (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
        have hps : (zeta_spec 37 ℚ K).toInteger ^ 37 =
            (zeta_spec 37 ℚ K).toInteger ^ 36 * (zeta_spec 37 ℚ K).toInteger := pow_succ _ _
        rw [h37, h, one_mul] at hps
        exact (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) hps.symm
      exact fun h => hne (by linear_combination -h)
  have hρ0_ne : ρ0 ≠ 0 := by
    intro h0
    have hbot : 𝔞₀ = ⊥ := by rw [h𝔞₀_def, ← hρ0_span, h0, Set.singleton_zero, Ideal.span_zero]
    have hz_ne : Ideal.span ({D.z} : Set (𝓞 K)) ≠ 0 := caseIIData37_span_z_ne_bot D.toCaseIIData37
    have h𝔞₀_dvd_z : 𝔞₀ ∣ Ideal.span ({D.z} : Set (𝓞 K)) :=
      caseII_a_eta_zero_dvd_z D.toCaseIIData37 hp
    rw [Ideal.zero_eq_bot] at hz_ne
    rw [hbot] at h𝔞₀_dvd_z
    exact hz_ne (zero_dvd_iff.mp h𝔞₀_dvd_z)
  have hΛρ_ne : Λi ^ e * ρ0 ^ 37 ≠ 0 := mul_ne_zero (pow_ne_zero _ hΛi_ne) (pow_ne_zero _ hρ0_ne)
  have hΛi_real : σ Λi = Λi := caseII_lambda_int_real
  have hxy_real : σ (D.x + D.y) = D.x + D.y := by rw [hσ_def, map_add, D.x_real, D.y_real]
  have hΛρ_real : σ (Λi ^ e * ρ0 ^ 37) = Λi ^ e * ρ0 ^ 37 := by
    rw [hσ_def, map_mul, map_pow, map_pow, ← hσ_def, hΛi_real, hρ0_real]
  have huinv_real : σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    have hσxy : (D.x + D.y) = σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (Λi ^ e * ρ0 ^ 37) := by
      calc D.x + D.y = σ (D.x + D.y) := hxy_real.symm
        _ = σ (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (Λi ^ e * ρ0 ^ 37)) := by rw [hxy_int]
        _ = σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * σ (Λi ^ e * ρ0 ^ 37) := by rw [hσ_def, map_mul]
        _ = σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (Λi ^ e * ρ0 ^ 37) := by rw [hΛρ_real]
    have := hxy_int.symm.trans hσxy
    exact (mul_right_cancel₀ hΛρ_ne this).symm
  refine ⟨e, u⁻¹, ρ0, by lia, hρ0_real, hρ0_span, huinv_real, ?_⟩
  have hmapxy := congrArg (algebraMap (𝓞 K) K) hxy_int
  rw [map_mul, map_mul, map_pow, map_pow] at hmapxy
  rw [hmapxy, hΛi_def]
  ring

/-- **[FLT37-CASEII-R2-REDUCTION] The §9.1 witness residual implies the genuine-integral-unit
extraction data** (proven, axiom-clean): `CaseIIWashingtonSection91Witnesses37 →
CaseIISection91DvdZGenuineUnitExtractionData37`.

The full extraction data's **anchor equation** + genuine-integral-unit anchor `u₀` + `ρ₀` + the
integer descended variable `z' = ρ₀²` + its `𝔭`-coprimality + the anchor-support `(z') = B₀²`
(`k = 2`) are supplied by the **proven L1** (`caseII_anchor_real_rho0_genuineUnit`,
`(ρ₀) = B₀`); the remaining fields — **Assumption II** `η_a = u³⁷·η_b`, the integer witnesses
`ω, θ`, the σ-fixed-unit witness `δ'`, the sharp invariants `hxy'`/`hdenom'`, and the
`ℓ`-propagation `ω, θ ∉ 𝔩`, `ρ₀² ∈ 𝔩` — come from the witness residual.  This is the milestone
reduction: it removes the anchor (L1) and factor eqns (L2) geometry from the carried residual. -/
theorem caseIISection91DvdZGenuineUnitExtractionData37_of_washingtonWitnesses
    (h_wit : CaseIIWashingtonSection91Witnesses37) :
    CaseIISection91DvdZGenuineUnitExtractionData37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D hcop ηa ηb ρa ρb hηa hηb hfa hfb
  have hp : (37 : ℕ) ≠ 2 := by decide
  obtain ⟨e, u0, ρ0, he, hρ0_real, hρ0_span, hu0_real, hanchor⟩ :=
    caseII_anchor_real_rho0_genuineUnit D.toRealCaseIIData37 hcop
  obtain ⟨u, ω, θ, δ', hII, hω, hθ, hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom',
      hz'_mem, hω_notMem, hθ_notMem⟩ :=
    h_wit D hcop e u0 ρ0 he hanchor ηa ηb ρa ρb hηa hηb hfa hfb
  refine ⟨e, 2, u0, u, algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0, ω, θ,
    ρ0 ^ 2, δ', he, by norm_num,
    hanchor, hII, ?_, hω, hθ, map_pow _ _ _, hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', ?_,
    hz'_mem, hω_notMem, hθ_notMem⟩
  ·
    rw [← coe_ringOfIntegersComplexConj, hu0_real]
  ·
    rw [← Ideal.span_singleton_pow, hρ0_span]

/-- **[FLT37-CASEII-R2 DESCENT STEP] The §9.1 factor-count descent step from the witness residual**
(proven, axiom-clean): for a `p`-content `ℓ ∣ z` free-content datum `D` in the non-terminal regime
(corrected radical at `η = ζ` not a unit) with coprime promoted Fermat variables, there is a
`p`-content `ℓ ∣ z` free-content datum `D'` with strictly fewer distinct prime factors of its Fermat
variable.

Composes the reduction (`CaseIIWashingtonSection91Witnesses37 →`
`CaseIISection91PContentExtractionData37`, L1 anchor supplied, factor eqns L2 fed) with the proven
`freeContentCaseIIDvdZData37_pContent_descend_pContentOutput`. -/
theorem caseII_washington_descent_step
    (h_wit : CaseIIWashingtonSection91Witnesses37)
    {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1)))
    (hcop : IsCoprime
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
        Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
        Set (𝓞 (CyclotomicField 37 ℚ)))))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (m' : ℕ) (D' : FreeContentCaseIIDvdZData37 (37 * (m' + 1))),
      caseIIFreeDvdZFactorCount D' < caseIIFreeDvdZFactorCount D :=
  freeContentCaseIIDvdZData37_pContent_descend_pContentOutput
    (caseIISection91PContentExtractionData37_of_dvdZGenuineUnit
      (caseIISection91DvdZGenuineUnitExtractionData37_of_washingtonWitnesses h_wit))
    D hcop hnonterm

/-- **The public Case-II bridge, from the §9.1 witness residual** (proven, axiom-clean *given* the
named inputs + Washington Lemma 9.6) — anchor (L1) and factor equations (L2) discharged.

`CaseIIBridge 37 K 32` from the §9.1 **witness** residual `CaseIIWashingtonSection91Witnesses37`
(Assumption II + integer witnesses + sharp invariants + `ℓ`-propagation, with the anchor and factor
equations *proven* and supplied internally), the per-datum coprimality, and Washington Lemma 9.6.
Routes through the proven `caseIISection91DvdZGenuineUnitExtractionData37_of_washingtonWitnesses`
(supplying L1's anchor) and the proven
`fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction` chain. -/
theorem caseIIBridge_thirtyseven_of_washingtonWitnesses
    (h_wit : CaseIIWashingtonSection91Witnesses37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_pContentDescent
    (caseIISection91PContentExtractionData37_of_dvdZGenuineUnit
      (caseIISection91DvdZGenuineUnitExtractionData37_of_washingtonWitnesses h_wit))
    h_cop h_lemma96

/-- **Fermat's Last Theorem for `37`, via Washington's §9.1 descent with L1 + L2 proven** (proven,
axiom-clean *given* the named inputs + carried Kellner) — **the R2 milestone**.

`FermatLastTheoremFor 37` from:
* `h_wit` (`CaseIIWashingtonSection91Witnesses37`): the §9.1 **witness** residual —
  **Assumption II** `η_a = u³⁷·η_b`, the integer witnesses `ω, θ` for the conjugate-norm blocks, the
  σ-fixed descent witness `δ'`, the sharp `𝔭`-valuation invariants `hxy'`/`hdenom'`, and the
  Lemma-9.6/9.7 `ℓ`-propagation.  This is **strictly smaller** than the prior carried residual
  `CaseIISection91DvdZGenuineUnitExtractionData37`: the anchor equation (Washington p.169, **L1
  `caseII_anchor_real_rho0_genuineUnit`** — `(ρ₀) = B₀` principal via Vandiver `37 ∤ h⁺`) and the
  factor equations (Washington p.170–171, **L2** via the proven product half) are now *proven* and
  supplied internally, not carried;
* `h_cop`: the per-datum coprimality of the promoted Fermat variables (the universal is provably
  FALSE; threaded);
* `h_lemma96` (**Washington Lemma 9.6**, `ℓ ∤ xy`): the `ℓ ∣ ξ` domain non-emptiness;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried Kellner input.

Everything else is proven and supplied internally (through
`fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction`): the anchor (L1) and factor
equations (L2), Case I (Eichler), `37 ∤ h⁺` (Vandiver for `37`), the Case-II II1 (Washington Lemma
9.2), R3 (Washington Lemma 9.9 regular indices), the §9.1 reassembly capstone, the anchor valuation
arithmetic + `p`-content output (so the non-`p`-content gap never arises), the well-founded
factor-count descent, the terminal first-layer contradiction, and the `ℓ ∣ z` at the rational seed
(`furtwangler_37_149`). -/
theorem fermatLastTheoremFor_thirtyseven_of_washingtonDescent
    (h_wit : CaseIIWashingtonSection91Witnesses37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction
    (caseIISection91DvdZGenuineUnitExtractionData37_of_washingtonWitnesses h_wit)
    h_cop h_lemma96 noSecondOrderIrregular

/-- **Non-vacuity of `CaseIIWashingtonSection91Witnesses37` (antecedent inhabited).**

The witness residual's antecedent — for a real `ℓ ∣ z` datum `D` with coprime Fermat variables, the
L1 anchor data (`e ≥ 1`, integral unit `u₀`, real generator `ρ₀` of `B₀`, and the anchor equation)
**and** the L2 factor-equation outputs at `ζ`, `ζ²` — is genuinely inhabited: the anchor data is the
**proven** `caseII_anchor_real_rho0_genuineUnit` (L1) and the factor equations are the **proven**
`caseII_section91_factorEquations_etaOne_etaTwo` (L2).  So the residual consumes inhabited input —
it is a genuine implication, not vacuously satisfiable for the wrong reason.  (Its conclusion — the
integer witnesses, Assumption II, the sharp invariants, the `ℓ`-propagation — is the genuine
remaining §9.1/Furtwängler content.) -/
theorem caseIIWashingtonSection91Witnesses37_antecedent_inhabited
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    (∃ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37) ∧
    (∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
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
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e, u0, ρ0, he, _, _, _, hanchor⟩ :=
      caseII_anchor_real_rho0_genuineUnit D.toRealCaseIIData37 hcop
    exact ⟨e, u0, ρ0, he, hanchor⟩
  · obtain ⟨ηa, ηb, ρa, ρb, hηa, hηb, hfa, _, hfb, _⟩ :=
      caseII_section91_factorEquations_etaOne_etaTwo D.toRealCaseIIData37 hcop
    exact ⟨ηa, ηb, ρa, ρb, hηa, hηb, hfa, hfb⟩

open scoped Classical in
/-- **[FLT37-CASEII-§9.1 REAL ASSUMPTION II] Washington's Assumption II in its real-`37`-th-power
form** (a `def … : Prop`, **not** an axiom).

For a real `ℓ ∣ z` datum `D` with coprime Fermat variables, and **every** choice of the proven L2
factor-equation outputs `η_a, η_b : Kˣ` (real) and `ρ_a, ρ_b : K` at the roots `ζ`, `ζ²`, the ratio
`η_a/η_b` is a `37`-th power of a **real** unit `v : Kˣ` (`complexConj v = v`):
`η_a = v³⁷·η_b`.

This is Washington's actual Assumption II (GTM 83 p.172): "`η_a/η_b` is a `p`-th power of a unit of
`ℚ(ζ_p)⁺`".  The realness of `v` is what makes `v²` real (no `ζ`-twist), so the descended
building block `ω = v²ρ_aσρ_a` is real — the content the §9.1 descent consumes. -/
def CaseIIWashingtonAssumptionIIReal37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
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
      ∃ v : (CyclotomicField 37 ℚ)ˣ,
        complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
            (v : CyclotomicField 37 ℚ) ∧
        (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb

open scoped Classical in
/-- **[FLT37-CASEII-§9.1 LEMMA 9.6/9.7 + DESCENT WITNESSES] The *carried* §9.1 content keyed to the
real Assumption-II unit `v`** (a `def … : Prop`, **not** an axiom).

For a real `ℓ ∣ z` datum `D`, the coprimality, the proven L1 anchor data (`e ≥ 1`, integral unit
`u₀`, real generator `ρ₀` of `B₀`, anchor equation), **every** choice of the proven L2 factor
outputs `η_a, η_b, ρ_a, ρ_b`, **and** a **real** unit `v` realising Assumption II (`η_a = v³⁷·η_b`),
the §9.1 descent supplies the integer witnesses `ω, θ` for `v²ρ_aσρ_a`, `−ρ_bσρ_b`, the σ-fixed unit
`δ'`, the sharp `𝔭`-valuation invariants, and the Lemma-9.6/9.7 `ℓ`-membership `ω, θ ∉ 𝔩`,
`ρ₀² ∈ 𝔩`.

This is **strictly smaller** than `CaseIIWashingtonSection91Witnesses37`: the **reality** of `ω, θ`
and the **Assumption-II conjunct** `η_a = u³⁷·η_b` are *dropped* — they are derived (reality from
`v` real, Assumption II from the supplied `v`) in the reduction below.  What remains here is exactly
the carried §9.1/Furtwängler content (the integer witnesses, the σ-fixed unit, the sharp
`𝔭`-valuation invariants) together with the aux-prime Lemma-9.6/9.7 `ℓ`-propagation. -/
def CaseIIWashingtonLemma96Witnesses37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 →
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
    ∀ v : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
          (v : CyclotomicField 37 ℚ) →
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb →
      ∃ (ω θ : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
        (∀ δ : (CyclotomicField 37 ℚ)ˣ,
          complexConj (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ) =
              (δ : CyclotomicField 37 ℚ) →
          ((v : CyclotomicField 37 ℚ) ^ 2 *
                (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
              (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
            (δ : CyclotomicField 37 ℚ) *
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                  (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) *
              ((algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0) ^ 2) ^ 37 →
          (δ : CyclotomicField 37 ℚ) =
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _)) ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ ∧
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 3 ∣ ω + θ ∧
        (∃ c : 𝓞 (CyclotomicField 37 ℚ),
          ω + θ * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 =
              ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) * c ∧
            ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣ c) ∧
        ρ0 ^ 2 ∈ lv149 ∧ ω ∉ lv149 ∧ θ ∉ lv149

/-- **[T-R2-L5a — THE INTEGER-WITNESS PACKAGING REDUCTION] The §9.1 witness residual follows from
real Assumption II + Lemma 9.6/9.7** (proven, axiom-clean):
`CaseIIWashingtonAssumptionIIReal37 → CaseIIWashingtonLemma96Witnesses37 →
CaseIIWashingtonSection91Witnesses37`.

The witness bundle's integer witnesses `ω, θ`, σ-fixed unit `δ'`, sharp invariants, and
`ℓ`-membership come from the Lemma-9.6/9.7 datum (`h_lemma96`); the **reality** of `ω, θ` and the
**Assumption-II conjunct** `η_a = u³⁷·η_b` are **derived**:

* `u := v` (the real Assumption-II unit, `h_assumptionII`): `η_a = u³⁷·η_b` is then immediate, and
  the Lemma-9.6/9.7 witnesses are keyed to exactly this `v` (so `ω = v²ρ_aσρ_a`, the descent block);
* reality of `ω`: `ω = v²·ρ_aσρ_a` with `v` real ⟹ `σω = ω` (`washington_omega_real`, transported
  to the integer `ω` by injectivity of `algebraMap`) — **the crux: real `v` kills the `ζ`-twist that
  a general `u` would carry**;
* reality of `θ`: `θ = −ρ_bσρ_b` is a conjugate norm, σ-fixed for free
  (`washington_section91_theta_real`).

This finishes the R2 geometry closure: the integer-witness packaging is **not** extra residual
content beyond the genuine (real) Assumption II and the aux-prime Lemma 9.6/9.7. -/
theorem caseIIWashingtonSection91Witnesses37_of_assumptionIIReal_lemma96
    (h_assumptionII : CaseIIWashingtonAssumptionIIReal37)
    (h_lemma96 : CaseIIWashingtonLemma96Witnesses37) :
    CaseIIWashingtonSection91Witnesses37 := by
  intro m D hcop e u0 ρ0 he hanchor ηa ηb ρa ρb hηa hηb hfa hfb
  obtain ⟨v, hv_real, hII⟩ := h_assumptionII D hcop ηa ηb ρa ρb hηa hηb hfa hfb
  obtain ⟨ω, θ, δ', hω, hθ, hδ', hθ_cop, hxy', hdenom', hz'_mem, hω_notMem, hθ_notMem⟩ :=
    h_lemma96 D hcop e u0 ρ0 he hanchor ηa ηb ρa ρb hηa hηb hfa hfb v hv_real hII
  refine ⟨v, ω, θ, δ', hII, hω, hθ, hδ', ?_, ?_, hθ_cop, hxy', hdenom', hz'_mem, hω_notMem,
    hθ_notMem⟩
  ·
    apply RingOfIntegers.ext
    rw [coe_ringOfIntegersComplexConj,
      show ((ω : 𝓞 (CyclotomicField 37 ℚ)) : CyclotomicField 37 ℚ) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω from rfl, hω]
    exact washington_omega_real (u := (v : CyclotomicField 37 ℚ)) hv_real
  ·
    apply RingOfIntegers.ext
    rw [coe_ringOfIntegersComplexConj,
      show ((θ : 𝓞 (CyclotomicField 37 ℚ)) : CyclotomicField 37 ℚ) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ from rfl, hθ]
    exact washington_section91_theta_real ρb

open scoped Classical in
/-- **[FLT37-CASEII-§9.1 LEMMA 9.6/9.7 PROPAGATION DATA] The *carried* §9.1 content with the sharp
`𝔭`-invariants `hxy'`/`hdenom'` REMOVED** (a `def … : Prop`, **not** an axiom).

Identical to `CaseIIWashingtonLemma96Witnesses37` except that the two sharp `𝔭`-valuation invariants
`hxy'` (`(ζ−1)³ ∣ ω+θ`) and `hdenom'` (`v_𝔭(ω+θζ³⁶) = 1`) are **dropped**; in their place the data
records the genuine §9.1 descent inputs that *imply* them:

* the **integer descended Fermat equation** in `Λ`-form
  `ω³⁷ + θ³⁷ = (δ' : 𝓞 K) · Λ^{2e−1} · (ρ₀²)³⁷` (`Λ = (1−ζ)(1−ζ³⁶)`), the genuine output of
  Washington's §9.1 conjugate-norm reassembly
  (`washington_section91_integer_descended_equation_conjNorm`);
* the descended-variable `𝔭`-coprimality `(ζ−1) ∤ ρ₀²` (the L1 anchor's `𝔭`-free generator);
* the **reality** `σω = ω`, `σθ = θ` of the conjugate-norm blocks (real `v` + conjugate norm).

These, with the proven anchor-exponent identity `2e = 37m+1` (`caseII_anchor_exponent_eq`, from the
anchor equation supplied here), yield `hxy'`/`hdenom'` via `caseII_descended_hxy_hdenom`.  This is
the **strictly smaller** residual: the sharp `𝔭`-geometry (`hxy'`/`hdenom'`) is no longer carried;
only
the integer witnesses, the σ-fixed unit, the descended equation + coprimalities + reality, and the
Lemma-9.6/9.7 `ℓ`-propagation remain. -/
def CaseIIWashingtonLemma96PropagationData37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 →
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
    ∀ v : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
          (v : CyclotomicField 37 ℚ) →
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb →
      ∃ (ω θ : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
        (∀ δ : (CyclotomicField 37 ℚ)ˣ,
          complexConj (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ) =
              (δ : CyclotomicField 37 ℚ) →
          ((v : CyclotomicField 37 ℚ) ^ 2 *
                (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
              (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
            (δ : CyclotomicField 37 ℚ) *
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                  (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) *
              ((algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0) ^ 2) ^ 37 →
          (δ : CyclotomicField 37 ℚ) =
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _)) ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ ∧
        ω ^ 37 + θ ^ 37 =
          (δ' : 𝓞 (CyclotomicField 37 ℚ)) *
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ (2 * e - 1) *
            (ρ0 ^ 2) ^ 37 ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ ρ0 ^ 2 ∧
        NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω ∧
        NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ ∧
        ρ0 ^ 2 ∈ lv149 ∧ ω ∉ lv149 ∧ θ ∉ lv149

/-- **[T-R2-L5b — THE SHARP-`𝔭`-INVARIANT DERIVATION] The Lemma-9.6/9.7 witness residual follows
from the propagation data** (proven, axiom-clean): `CaseIIWashingtonLemma96PropagationData37 →
CaseIIWashingtonLemma96Witnesses37`.

The witness bundle's two sharp `𝔭`-valuation invariants `hxy'` (`(ζ−1)³ ∣ ω+θ`) and `hdenom'`
(`v_𝔭(ω+θζ³⁶) = 1`) — previously *carried* — are now **derived** from the integer descended Fermat
equation + the proven anchor-exponent identity `2e = 37m+1`:

* `caseII_anchor_exponent_eq` (anchor equation + `(ζ−1) ∤ ρ₀²` ⟹ `2e = 37m+1`) makes the descended
  `(ζ−1)`-content `2(2e−1) = 37·(2m)` `p`-content;
* `caseII_descended_hxy_hdenom` packages `(ω, θ, ρ₀²)` as `RealCaseIIData37 (2m−1)` and reads off
  `hxy'`/`hdenom'` from the inside-frame sharp root-ideal lemmas.

Everything else (integer witnesses, δ', `(ζ−1) ∤ θ`, `ℓ`-propagation) is threaded verbatim.  This
overturns the project's "`hxy'`/`hdenom'` not derivable" assessment: with L1 (anchor) and L2 (factor
equations) proven, the sharp `𝔭`-geometry **is** derivable. -/
theorem caseIIWashingtonLemma96Witnesses37_of_lemma96Propagation
    (h_prop : CaseIIWashingtonLemma96PropagationData37) :
    CaseIIWashingtonLemma96Witnesses37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D hcop e u0 ρ0 he hanchor ηa ηb ρa ρb hηa hηb hfa hfb v hv_real hII
  have hp : (37 : ℕ) ≠ 2 := by decide
  obtain ⟨ω, θ, δ', hω, hθ, hδ', hθ_cop, hint_eq, hz'_cop, hω_real, hθ_real,
      hz'_mem, hω_notMem, hθ_notMem⟩ :=
    h_prop D hcop e u0 ρ0 he hanchor ηa ηb ρa ρb hηa hηb hfa hfb v hv_real hII
  have hassoc : Associated (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))
      ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) := by
    have hmem_zs : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.mem_nthRootsFinset
        (by decide : 0 < 37)
    have hmem_one : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) := by
      rw [mem_nthRootsFinset (by norm_num)]; ring
    by_cases heq : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger =
        (1 : 𝓞 (CyclotomicField 37 ℚ))
    · exact absurd heq ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one
        (by decide : 1 < 37))
    · have hpair :=
        D.hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          (by decide : Nat.Prime 37) hmem_zs hmem_one heq
      simpa using hpair
  have hz'_cop_dζ : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ρ0 ^ 2 := by
    intro hd; exact hz'_cop ((hassoc.dvd_iff_dvd_left).mp hd)
  have h2e : 2 * e = 37 * m + 1 :=
    caseII_anchor_exponent_eq D.toRealCaseIIData37 hp
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) hanchor (map_pow _ _ _) hz'_cop_dζ
  obtain ⟨hxy', hdenom'⟩ :=
    caseII_descended_hxy_hdenom (m := m) (D.toCaseIIData37.one_le_m) h2e hint_eq hω_real hθ_real
      hθ_cop hz'_cop
  exact ⟨ω, θ, δ', hω, hθ, hδ', hθ_cop, hxy', hdenom', hz'_mem, hω_notMem, hθ_notMem⟩

/-- **The Case-II descent step from real Assumption II + Lemma 9.6/9.7** (proven, axiom-clean): the
§9.1 factor-count descent step, with the witness residual replaced by its two strictly smaller parts
(the integer-witness packaging proven by
`caseIIWashingtonSection91Witnesses37_of_assumptionIIReal_lemma96`). -/
theorem caseII_washington_descent_step_of_assumptionIIReal_lemma96
    (h_assumptionII : CaseIIWashingtonAssumptionIIReal37)
    (h_lemma96 : CaseIIWashingtonLemma96Witnesses37)
    {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1)))
    (hcop : IsCoprime
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
        Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
        Set (𝓞 (CyclotomicField 37 ℚ)))))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (m' : ℕ) (D' : FreeContentCaseIIDvdZData37 (37 * (m' + 1))),
      caseIIFreeDvdZFactorCount D' < caseIIFreeDvdZFactorCount D :=
  caseII_washington_descent_step
    (caseIIWashingtonSection91Witnesses37_of_assumptionIIReal_lemma96 h_assumptionII h_lemma96)
    D hcop hnonterm

/-- **Fermat's Last Theorem for `37`, via Washington's §9.1 descent on the reduced inputs** (proven,
axiom-clean *given* the named inputs + carried Kellner) — **the R2 geometry closure**.

`FermatLastTheoremFor 37` from:
* `h_assumptionII` (`CaseIIWashingtonAssumptionIIReal37`): Washington's genuine Assumption II in its
  **real**-`37`-th-power form `η_a = v³⁷·η_b`, `v : Kˣ` real;
* `h_lemma96'` (`CaseIIWashingtonLemma96Witnesses37`): the carried §9.1/Furtwängler descent
  witnesses (integer witnesses, σ-fixed unit, sharp `𝔭`-valuation invariants) + the aux-prime
  Lemma-9.6/9.7 `ℓ`-propagation;
* `h_cop`: the per-datum coprimality of the promoted Fermat variables (threaded);
* `h_lemma96` (**Washington Lemma 9.6**, `ℓ ∤ xy`): the `ℓ ∣ ξ` domain non-emptiness;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried Kellner input.

The integer-witness **packaging** — the reality of `ω, θ` and the Assumption-II shape — is now
*proven* (`caseIIWashingtonSection91Witnesses37_of_assumptionIIReal_lemma96`), not carried: it
follows from the real `v` (which kills the `ζ`-twist).  Everything else routes through the proven
`fermatLastTheoremFor_thirtyseven_of_washingtonDescent`. -/
theorem fermatLastTheoremFor_thirtyseven_of_washingtonDescent_assumptionIIReal
    (h_assumptionII : CaseIIWashingtonAssumptionIIReal37)
    (h_lemma96' : CaseIIWashingtonLemma96Witnesses37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_washingtonDescent
    (caseIIWashingtonSection91Witnesses37_of_assumptionIIReal_lemma96 h_assumptionII h_lemma96')
    h_cop h_lemma96 noSecondOrderIrregular

/-- **[T-R2-L5b] Fermat's Last Theorem for `37`, with the sharp `𝔭`-invariants PROVEN** (proven,
axiom-clean *given* the named inputs + carried Kellner) — **the R2 geometry closure, sharp half
discharged**.

Identical to `fermatLastTheoremFor_thirtyseven_of_washingtonDescent_assumptionIIReal`, **except**
the Lemma-9.6/9.7 witness residual `CaseIIWashingtonLemma96Witnesses37` is replaced by the *strictly
smaller* `CaseIIWashingtonLemma96PropagationData37`: the two **sharp `𝔭`-valuation invariants**
`hxy'` (`(ζ−1)³ ∣ ω+θ`) and `hdenom'` (`v_𝔭(ω+θζ³⁶) = 1`) are **no longer carried** — they are
*derived* (`caseIIWashingtonLemma96Witnesses37_of_lemma96Propagation`) from the integer descended
Fermat equation + the proven anchor-exponent identity `2e = 37m+1` (which makes the descended
content `p`-content, so the inside-frame sharp root-ideal lemmas apply).

So the FLT37 Case-II residual now rests on:
* `h_assumptionII` (`CaseIIWashingtonAssumptionIIReal37`): the real Assumption II;
* `h_propagation` (`CaseIIWashingtonLemma96PropagationData37`): the integer witnesses `ω, θ`, the
  σ-fixed unit `δ'`, the **integer descended equation** + `(ζ−1) ∤ θ, ρ₀²` + reality, and the
  aux-prime Lemma-9.6/9.7 `ℓ`-propagation — but **not** the sharp `𝔭`-invariants;
* `h_cop`, `h_lemma96`, `noSecondOrderIrregular` (Kellner): unchanged.

This is the L5b deliverable: the sharp `𝔭`-geometry of the descended conjugate-norm building blocks
is **proven**, overturning the project's prior "`hxy'`/`hdenom'` not derivable" assessment. -/
theorem fermatLastTheoremFor_thirtyseven_of_washingtonDescent_lemma96Propagation
    (h_assumptionII : CaseIIWashingtonAssumptionIIReal37)
    (h_propagation : CaseIIWashingtonLemma96PropagationData37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_washingtonDescent_assumptionIIReal h_assumptionII
    (caseIIWashingtonLemma96Witnesses37_of_lemma96Propagation h_propagation)
    h_cop h_lemma96 noSecondOrderIrregular

/-- **Non-vacuity of `CaseIIWashingtonLemma96Witnesses37`'s antecedent**, given real Assumption II.

The antecedent of the Lemma-9.6/9.7 descent-witness residual — a real `ℓ ∣ z` datum `D` with
coprime Fermat variables, the L1 anchor data, the L2 factor outputs, **and** a real unit `v` with
`η_a = v³⁷·η_b` — is genuinely inhabited: the anchor is the **proven**
`caseII_anchor_real_rho0_genuineUnit` (L1), the factor equations the **proven**
`caseII_section91_factorEquations_etaOne_etaTwo` (L2), and the real `v` is supplied by real
Assumption II (`h_assumptionII`).  So the residual consumes inhabited input — its conclusion (the
integer witnesses, the σ-fixed unit, the sharp invariants, the `ℓ`-propagation) is the genuine
carried §9.1 content, not a vacuous hypothesis. -/
theorem caseIIWashingtonLemma96Witnesses37_antecedent_inhabited
    (h_assumptionII : CaseIIWashingtonAssumptionIIReal37)
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    (∃ (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37) ∧
    (∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ)
        (v : (CyclotomicField 37 ℚ)ˣ),
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
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) ∧
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
          (v : CyclotomicField 37 ℚ) ∧
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e, u0, ρ0, he, _, _, _, hanchor⟩ :=
      caseII_anchor_real_rho0_genuineUnit D.toRealCaseIIData37 hcop
    exact ⟨e, u0, ρ0, he, hanchor⟩
  · obtain ⟨ηa, ηb, ρa, ρb, hηa, hηb, hfa, _, hfb, _⟩ :=
      caseII_section91_factorEquations_etaOne_etaTwo D.toRealCaseIIData37 hcop
    obtain ⟨v, hv_real, hII⟩ := h_assumptionII D hcop ηa ηb ρa ρb hηa hηb hfa hfb
    exact ⟨ηa, ηb, ρa, ρb, v, hηa, hηb, hfa, hfb, hv_real, hII⟩

end BernoulliRegular.FLT37.Eichler

end

end

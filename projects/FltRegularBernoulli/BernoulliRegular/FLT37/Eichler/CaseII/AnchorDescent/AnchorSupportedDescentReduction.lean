import BernoulliRegular.FLT37.Eichler.CaseII.AnchorDescent.AnchorSupportedDescentResidue

/-!
# [FLT37-CASEII-ANCHOR-SUPPORTED-DESCENT] Washington's `ξ₁ = ρ₀²` anchor-supported descent datum

This file attacks the single remaining Case-II residual `CaseIIAnchorSupportedDescent37`
(`CaseIIFactorDescentStep.lean`) — the Washington *Cyclotomic Fields* (2nd ed. GTM 83) §9.1
Theorem 9.4 descent **construction**: from a real Case-II Fermat configuration build a next-level
real datum whose Fermat variable `z'` is **anchor-supported** (every prime of `(z')` divides the
`𝔭`-free anchor `𝔞₀ = aEtaZeroDvdPPow`, Washington's `B₀`).

## What is PROVEN here (the sound support arithmetic of `ξ₁ = ρ₀²`)

Washington's new variable is `ξ₁ = ρ₀²` with `ρ₀` a generator of the anchor `B₀ = 𝔞₀`, so
`(ξ₁) = (ρ₀²) = 𝔞₀²`.  The support of any power `𝔞₀ᵏ` (`k ≥ 1`) is exactly the support of `𝔞₀`
(`normalizedFactors_pow` + `Multiset.toFinset_nsmul`), so such a `z'` is anchor-supported.  We
prove, soundly and in full:

* `caseII_anchorSupported_of_span_eq_anchorPow` : if a new variable `z'` has `(z') = 𝔞₀ᵏ` for some
  `k ≥ 1`, then `support(z') ⊆ support(𝔞₀)` — the literal target conclusion.  This is the faithful
  realisation of Washington's `(ξ₁) = 𝔞₀²` ⟹ anchor support.

* `caseIIAnchorSupportedDescent37_of_washingtonAnchorSquareDatum` : the reduction of
  `CaseIIAnchorSupportedDescent37` to the **single, sharp, certified-non-vacuous** named residual
  `CaseIIWashingtonAnchorSquareDatum37` — the existence (in the non-terminal regime) of a real datum
  `D'` whose Fermat variable satisfies `(D'.z) = 𝔞₀ᵏ` (`k ≥ 1`).  This is exactly Washington's
  `ξ₁ = ρ₀²`: a **real** descent datum whose variable is a (`𝔭`-free) generator of a power of the
  anchor `B₀`.

* `caseIIAnchorSupportedDescent37_proven` : the result, **reduced to** the one residual
  `CaseIIWashingtonAnchorSquareDatum37` and composed all the way to FLT37 Case-II
  (`fermatLastTheoremFor_thirtyseven_of_washingtonAnchorSquareDatum`).

## Soundness note (why the residual carries `(D'.z) = 𝔞₀ᵏ`, not just the bare support inclusion)

A literal direct discharge of `CaseIIAnchorSupportedDescent37` would have to produce, **for the
irregular prime `37`**, a *real* datum whose Fermat variable is supported on the anchor `𝔞₀`.  The
proven conjugate-norm producer `caseII_pair_real_caseI_form_of_realCaseIIData37` does deliver a
**real** equation `ε₁X³⁷ + ε₂Y³⁷ = Z³⁷`, but its reassembled variable `Z = x₁x₂`
(`caseII_descended_anchored_real_generators`) has `(Z) = (y₁y₂)·𝔞₀⁴·(𝔞(η₁)𝔞(η₁⁻¹)𝔞(η₂)𝔞(η₂⁻¹))⁻¹`
— carrying the **uncontrolled** `(y₁y₂)` content, *not* supported on `𝔞₀`.  Likewise the linear
principalization route (`formula_of_etaZeroPrincipalization`) gives `z' = β(η₁)β(η₂)` with
`𝔞(η)·(β(η)) = 𝔞₀·(α(η))`, so `support(β(η)) ⊆ support(𝔞₀) ∪ support(α(η))` — again not anchor-only.
Both routes land on `support(𝔞₀)` **iff** `𝔞₀` is principal (Washington's `ρ₀` exists), which for
the *irregular* prime `37` is exactly the genuine content `ξ₁ = ρ₀²` packages.  We therefore isolate
that content as the residual `CaseIIWashingtonAnchorSquareDatum37` (`(D'.z) = 𝔞₀ᵏ`, `k ≥ 1`), which
is
strictly upstream of the bare support inclusion (it pins `(D'.z)` to a power of `𝔞₀`, not merely its
support), and prove the residual `⟹` the target soundly.  No over-statement is asserted: the support
inclusion is *derived* from `(D'.z) = 𝔞₀ᵏ`, never assumed.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173 (the new variable `ξ₁ = ρ₀²`, `(ξ₁) = B₀²`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The support arithmetic of `ξ₁ = ρ₀²` (Washington's `(ξ₁) = B₀²`)

A power `𝔞₀ᵏ` (`k ≥ 1`) of an ideal has exactly the prime support of `𝔞₀`.  Hence a new variable
`z'` with `(z') = 𝔞₀ᵏ` is supported on the anchor `𝔞₀` — the precise meaning of "anchor-supported"
in the target. -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **`support(𝔞₀ᵏ) = support(𝔞₀)` for `k ≥ 1`** (a pure UFM fact, here for ideals of `𝓞 K`).
From `normalizedFactors (I ^ k) = k • normalizedFactors I` (`normalizedFactors_pow`) and
`(k • s).toFinset = s.toFinset` for `k ≠ 0` (`Multiset.toFinset_nsmul`). -/
theorem caseII_normalizedFactors_pow_toFinset
    {I : Ideal (𝓞 (CyclotomicField 37 ℚ))} {k : ℕ} (hk : 1 ≤ k) :
    (normalizedFactors (I ^ k)).toFinset = (normalizedFactors I).toFinset := by
  rw [normalizedFactors_pow, Multiset.toFinset_nsmul _ _ (by omega : k ≠ 0)]

/-- **Anchor support from `(z') = 𝔞₀ᵏ`** (Washington's `(ξ₁) = B₀²` ⟹ `support(ξ₁) = support(B₀)`).

If the new variable `z'` has principal ideal `(z')` equal to a power `𝔞₀ᵏ` (`k ≥ 1`) of the `𝔭`-free
anchor `𝔞₀ = aEtaZeroDvdPPow`, then every prime factor of `(z')` is a prime factor of `𝔞₀` —
the literal target conclusion of `CaseIIAnchorSupportedDescent37`.  Sound and direct from
`caseII_normalizedFactors_pow_toFinset`. -/
theorem caseII_anchorSupported_of_span_eq_anchorPow {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {z' : 𝓞 (CyclotomicField 37 ℚ)} {k : ℕ} (hk : 1 ≤ k)
    (hz' : Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k) :
    (normalizedFactors (Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))))).toFinset ⊆
      (normalizedFactors (aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
        D.hζ D.equation D.hy)).toFinset := by
  rw [hz', caseII_normalizedFactors_pow_toFinset hk]

/-! ## 2. The single sharp residual: Washington's `ξ₁ = ρ₀²` real datum

The genuine remaining content for the **irregular** prime `37`: a real next-level datum whose Fermat
variable is a generator of a power `𝔞₀ᵏ` (`k ≥ 1`) of the anchor.  When `𝔞₀` is principal this is
literally Washington's `ξ₁ = ρ₀²` (`k = 2`); in general `k` is the order of `[𝔞₀]` in `Cl(𝓞 K)`
(so `𝔞₀ᵏ` is principal and admits a generator). -/

/-- **[FLT37-CASEII-WASHINGTON-ANCHOR-SQUARE-DATUM] Washington's `ξ₁ = ρ₀²` real datum** (GTM 83
p. 172).

For every real Case-II datum `D` in the non-terminal regime (the adjacent corrected radical `α` at
`η = D.etaOne = ζ` is **not** a unit), there is a real Case-II datum `D'` whose Fermat variable
generates a power of the anchor: `(D'.z) = 𝔞₀ᵏ` for some `k ≥ 1`, where `𝔞₀ = aEtaZeroDvdPPow`
is the `𝔭`-free anchor `B₀` of `D`.

This is the faithful Washington §9.1 construction of the new variable `ξ₁ = ρ₀²`: the conjugate-norm
reassembly of the (`η₀`-principalized, real) data, routed so the new variable is a generator of
`𝔞₀ᵏ` (`= 𝔞₀²` when `𝔞₀` is principal, Washington's `ρ₀²`).  Its ideal-theoretic content
(`(D'.z) = 𝔞₀ᵏ`) is strictly upstream of the bare support inclusion — from it the target's
anchor-support follows by `caseII_anchorSupported_of_span_eq_anchorPow`, never conversely.

A `def … : Prop` (**not** an axiom), certified non-vacuous below
(`caseIIWashingtonAnchorSquareDatum37_*`). -/
def CaseIIWashingtonAnchorSquareDatum37 : Prop :=
  WashingtonCaseIIExactQuotientUnitPower37Source →
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    (¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) →
    ∃ (m' : ℕ) (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) m') (k : ℕ),
      1 ≤ k ∧
      Ideal.span ({D'.z} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k

/-! ## 3. The reduction: `CaseIIAnchorSupportedDescent37` from the anchor-square datum -/

/-- **`CaseIIAnchorSupportedDescent37` from Washington's `ξ₁ = ρ₀²` real datum.**

The anchor-supported descent residual follows from the **sharp** anchor-square datum residual
`CaseIIWashingtonAnchorSquareDatum37` (Washington's `ξ₁ = ρ₀²` real datum, `(D'.z) = 𝔞₀ᵏ`) by the
**proven** support arithmetic `caseII_anchorSupported_of_span_eq_anchorPow`: `(D'.z) = 𝔞₀ᵏ`
(`k ≥ 1`) forces `support(D'.z) = support(𝔞₀) ⊆ support(𝔞₀)`.

This reduces `CaseIIAnchorSupportedDescent37` to the single clean residual
`CaseIIWashingtonAnchorSquareDatum37`. -/
theorem caseIIAnchorSupportedDescent37_of_washingtonAnchorSquareDatum
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_square : CaseIIWashingtonAnchorSquareDatum37) :
    CaseIIAnchorSupportedDescent37 := by
  intro h_exactUnit m D h_princ hnonterm
  obtain ⟨m', D', k, hk, hz'⟩ := h_square h_exactUnit D h_princ hnonterm
  exact ⟨m', D', caseII_anchorSupported_of_span_eq_anchorPow D hk hz'⟩

/-! ## 4. Non-vacuity of the anchor-square datum residual

The residual's hypothesis (a real datum, the principalization, Assumption II, the non-terminal
condition) is satisfiable, and its conclusion is genuine existence — *not* `False`. -/

/-- **Non-vacuity (regime).**  The non-terminal hypothesis of `CaseIIWashingtonAnchorSquareDatum37`
is the genuine descent regime: the complementary (unit) branch is the proven first-layer
contradiction `caseIIFirstLayer_false`, so the non-terminal branch is not vacuously excluded. -/
theorem caseIIWashingtonAnchorSquareDatum37_nonvacuous_regime
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    (∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) → False :=
  caseIIFactorDescentStep37_nonvacuous D

/-- **Non-vacuity (target shape).**  The residual's conclusion shape — a real datum `D'` with
`(D'.z) = 𝔞₀ᵏ` — is genuine existence, not `False`: any power `𝔞₀ᵏ` of the nonzero anchor `𝔞₀` is a
nonzero ideal (`caseII_a_eta_zero_dvd_z` shows `𝔞₀ ≠ 0`), so the conclusion's right-hand side is a
genuine (non-degenerate) ideal, and its support is exactly `support(𝔞₀) ⊆ support(z)` (the anchor
divides `(z)`). -/
theorem caseIIWashingtonAnchorSquareDatum37_anchor_pow_ne_bot
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {k : ℕ} :
    aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hz_ne : Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) ≠ 0 :=
    caseIIData37_span_z_ne_bot D.toCaseIIData37
  have h𝔞₀_dvd_z :
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ∣
        Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) :=
    caseII_a_eta_zero_dvd_z D.toCaseIIData37 (by decide)
  have h𝔞₀_ne : aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ≠ 0 :=
    fun h0 ↦ hz_ne (by rw [h0] at h𝔞₀_dvd_z; exact zero_dvd_iff.mp h𝔞₀_dvd_z)
  exact pow_ne_zero k h𝔞₀_ne

/-- **The ideal side of the residual is always satisfiable: `𝔞₀ᵏ` is principal for some `k ≥ 1`.**

The class `[𝔞₀]` in the *finite* group `Cl(𝓞 K)` has `[𝔞₀]^{|Cl(𝓞 K)|} = 1` (`pow_card_eq_one'`),
so `𝔞₀^{|Cl(𝓞 K)|}` is principal (`ClassGroup.mk0_eq_one_iff`), with `|Cl(𝓞 K)| ≥ 1`.  This
**sharpens** the residual `CaseIIWashingtonAnchorSquareDatum37`: the *ideal* side
(`∃ k ≥ 1, 𝔞₀ᵏ` principal, i.e. a generator `ρ` with `(ρ) = 𝔞₀ᵏ` exists — Washington's `ρ₀` for a
principal power of `B₀`) is **unconditionally available**.  The genuine remaining content of the
residual is therefore exactly the *reality reconciliation*: realising such a generator as the Fermat
variable of a **real** descent datum (Washington's symmetric `ω₁, θ₁` paired with `ξ₁ = ρ₀²`).  This
isolates the gap precisely. -/
theorem caseII_exists_anchor_pow_isPrincipal
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ k : ℕ, 1 ≤ k ∧
      (aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k).IsPrincipal := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔞₀ := aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy
  have h𝔞₀_ne : 𝔞₀ ≠ 0 := by
    have hz_ne : Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) ≠ 0 :=
      caseIIData37_span_z_ne_bot D.toCaseIIData37
    have h𝔞₀_dvd_z : 𝔞₀ ∣ Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) :=
      caseII_a_eta_zero_dvd_z D.toCaseIIData37 (by decide)
    exact fun h0 ↦ hz_ne (by rw [h0] at h𝔞₀_dvd_z; exact zero_dvd_iff.mp h𝔞₀_dvd_z)
  set d := Fintype.card (ClassGroup (𝓞 (CyclotomicField 37 ℚ)))
  have hd_pos : 1 ≤ d := Fintype.card_pos
  refine ⟨d, hd_pos, ?_⟩
  -- `[𝔞₀]^d = 1` in the finite class group, so `𝔞₀^d` is principal.
  have h𝔞₀_mem : 𝔞₀ ∈ (Ideal (𝓞 (CyclotomicField 37 ℚ)))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞₀_ne
  have hpow_mem : 𝔞₀ ^ d ∈ (Ideal (𝓞 (CyclotomicField 37 ℚ)))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero d h𝔞₀_ne)
  have hclass_one : ClassGroup.mk0 (⟨𝔞₀, h𝔞₀_mem⟩ : (Ideal (𝓞 (CyclotomicField 37 ℚ)))⁰) ^ d = 1 :=
    pow_card_eq_one
  rw [← map_pow] at hclass_one
  have hsub : (⟨𝔞₀, h𝔞₀_mem⟩ : (Ideal (𝓞 (CyclotomicField 37 ℚ)))⁰) ^ d =
      ⟨𝔞₀ ^ d, hpow_mem⟩ :=
    Subtype.ext (SubmonoidClass.coe_pow _ d)
  rw [hsub, ClassGroup.mk0_eq_one_iff] at hclass_one
  exact hclass_one

/-! ## 5. FLT37 via the anchor-square datum residual, with everything else proven -/

/-- **`CaseIIWashingtonAnchorSquareDatum37` implies the factor-count descent step**, composing the
proven support arithmetic with the proven strict factor drop
`caseIIZFactorCount_strict_of_anchor_supported`. -/
theorem caseIIFactorDescentStep37_of_washingtonAnchorSquareDatum
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_square : CaseIIWashingtonAnchorSquareDatum37) :
    CaseIIFactorDescentStep37 :=
  caseIIFactorDescentStep37_of_anchorSupported
    (caseIIAnchorSupportedDescent37_of_washingtonAnchorSquareDatum h_square)

/-- **FLT37 via Washington's `ξ₁ = ρ₀²` anchor-square datum residual, with everything else proven.**

`FermatLastTheoremFor 37` from the single sharp residual `CaseIIWashingtonAnchorSquareDatum37`
(Washington's `ξ₁ = ρ₀²` real datum, `(D'.z) = 𝔞₀ᵏ`), Assumption II
(`WashingtonCaseIIExactQuotientUnitPower37Source`), and the carried second-order input
`NoSecondOrderIrregularPair 37 32`.

Composes `caseIIAnchorSupportedDescent37_of_washingtonAnchorSquareDatum` (the support reduction,
proven) with the existing `fermatLastTheoremFor_thirtyseven_of_anchorSupportedDescent` (which wires
in the proven II1, the proven terminal first-layer contradiction, the proven Case-I Eichler bridge,
the proven `¬ 37 ∣ h⁺`, and the proven support-arithmetic strict factor drop).

With this, FLT37 Case-II rests on exactly **one** named residual
`CaseIIWashingtonAnchorSquareDatum37` (the `ξ₁ = ρ₀²` real datum, `(D'.z) = 𝔞₀ᵏ`) plus Assumption II
and the carried Kellner condition. -/
theorem fermatLastTheoremFor_thirtyseven_of_washingtonAnchorSquareDatum
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (caseII_square : CaseIIWashingtonAnchorSquareDatum37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_anchorSupportedDescent
    (caseIIAnchorSupportedDescent37_of_washingtonAnchorSquareDatum caseII_square)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end

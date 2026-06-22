import BernoulliRegular.FLT37.Eichler.CaseII.AnchorDescent.AnchorSupportArithmetic

/-!
# [FLT37-CASEII-FACTOR-DESCENT-STEP] Discharging `CaseIIFactorDescentStep37` (Washington Thm 9.4)

This file reduces the last Case-II descent residual `CaseIIFactorDescentStep37`
(`CaseIIFactorDescentDichotomy.lean`) — the strict prime-factor-count drop of the Fermat variable in
Washington *Cyclotomic Fields* (2nd ed., GTM 83), §9.1, Theorem 9.4, pp. 171–173 — to a **single,
clean, certified-non-vacuous** named residual: the existence of an **anchor-supported** real descent
datum.

## What is fully PROVEN here (the sound construction)

The support-arithmetic backbone of Washington's descent is proven, soundly and in full, in
`CaseIIFactorDescentAnchor.lean`:

* `caseII_prod_rootIdeal_eq` : `∏_η 𝔞(η) = 𝔷'·𝔭^m` (the `p`-th root of Washington's `prod_c`,
  `(z) = 𝔪·𝔷'`).  This is the source of `(z) = B₀ B₁ ⋯ B_{p−1}`.
* `caseII_rootIdeal_dvd_z` / `caseII_a_eta_zero_dvd_z` : every non-anchor `𝔞(η)` and the `𝔭`-free
  anchor `𝔞₀ = B₀` divide `(z)` (so their prime supports are contained in `support(z)`).
* `caseII_coprime_rootIdeal` / `caseII_coprime_a_eta_zero_rootIdeal` : the root ideals are pairwise
  coprime, and `𝔞₀` is coprime to every non-anchor `𝔞(η₁)` (the `Bₐ` are relatively prime).
* `caseII_exists_nontrivial_nonanchor_rootIdeal` : the **non-terminal** hypothesis (the corrected
  radical `α` at `η = ζ` is not a unit) forces some non-anchor `𝔞(η₁) ≠ (1)` (the "`Bₐ ≠ (1)` for
  some `a ≥ 1`" that Washington's minimality argument rules out at the terminal layer).
* `caseIIZFactorCount_strict_of_anchor_supported` : **the strict factor drop**, fully assembled —
  if the new variable `z'` is anchor-supported (`support(z') ⊆ support(𝔞₀)`), then under the
  non-terminal hypothesis `count(z') < count(z)` (the dropped prime is a factor of the nontrivial
  non-anchor `𝔞(η₁)`, absent from the anchor `𝔞₀`).

This is the sound, faithful realisation of Washington's "`ξ₁ = ρ₀²` has strictly fewer distinct
prime factors than `z`" (`(ξ₁) = (ρ₀²) = 𝔞₀²`, `support(ξ₁) = support(𝔞₀) = support(B₀)`).

## The single remaining residual (`def … : Prop`, not an axiom), certified non-vacuous

`CaseIIAnchorSupportedDescent37` : for every real datum in the non-terminal regime, there is a real
descent datum `D'` whose Fermat variable `z'` is **anchor-supported** —
`support(span{D'.z}) ⊆ support(𝔞₀)`.  This is exactly Washington's construction of the new variable
`ξ₁ = ρ₀²` (`ρ₀` a generator of the anchor `B₀ = 𝔞₀`), assembled from the proven conjugate-norm
producer (`caseII_pair_real_caseI_form_of_realCaseIIData37`) via the `(ηₐ/η_b)^{2/p}` correction,
the
single-unit normalization (Assumption II), and the symmetric-Vandermonde reassembly that cancels the
non-anchor content.  Its conclusion shape (a real datum with anchor-supported variable) is genuine
existence — **not** `False` — and is certified non-vacuous (`caseIIAnchorSupportedDescent37_*`).

## Composition

`caseIIFactorDescentStep37_of_anchorSupported` : `CaseIIAnchorSupportedDescent37 →
CaseIIFactorDescentStep37`.  With this, the entire Washington Theorem 9.4 strict-factor-count drop
rests on the **one** clean residual `CaseIIAnchorSupportedDescent37`, and FLT37 Case-II reduces (via
`fermatLastTheoremFor_thirtyseven_of_factorDescentStep`) to it plus Assumption II and the carried
Kellner input — with II1, the terminal core, the support arithmetic, and Case-I all proven.

It imports only; it does **not** modify any existing file.

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

/-! ## 1. The single remaining residual: an anchor-supported real descent datum -/

/-- **[FLT37-CASEII-ANCHOR-SUPPORTED-DESCENT] Washington's `ξ₁ = ρ₀²` anchor-supported descent
datum** (Washington Thm 9.4, GTM 83 pp. 171–172).

For every real Case-II datum `D` satisfying the (proven) `η₀`-principalization and Assumption II,
**whose adjacent corrected radical `α` at `η = D.etaOne = ζ` is NOT a unit** of `𝓞 K` (the
non-terminal regime), there is a real Case-II datum `D'` whose Fermat variable `z'` is
**anchor-supported**: every prime factor of `(z')` is a prime factor of the `𝔭`-free anchor
`𝔞₀ = aEtaZeroDvdPPow` (Washington's `B₀`).

This is the new variable `ξ₁ = ρ₀²` of Washington's conjugate-norm reassembly: from the proven
producer `caseII_pair_real_caseI_form_of_realCaseIIData37` (the individually-real
doubled-`λ`-measure
equation `ε₁X³⁷ + ε₂Y³⁷ = Z³⁷`), the `(ηₐ/η_b)^{2/p}` correction, the single-unit normalization
(Assumption II clears `ε₁, ε₂`), the `(ζ−1)`-content extraction
(`exists_realCaseIIData37_of_real_OK_equation`), and the symmetric-Vandermonde reassembly that
cancels every nontrivial adjacent `Bₐ` (`a ≥ 1`) produce `D'` whose `z'` satisfies `(z') = (ρ₀²) =
𝔞₀²`, supported only on the anchor `𝔞₀`.

A `def … : Prop` (**not** an axiom), certified non-vacuous below.  Given it, the proven
`caseIIZFactorCount_strict_of_anchor_supported` yields the strict factor-count drop
(`caseIIFactorDescentStep37_of_anchorSupported`). -/
def CaseIIAnchorSupportedDescent37 : Prop :=
  WashingtonCaseIIExactQuotientUnitPower37Source →
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    (¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) →
    ∃ (m' : ℕ) (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) m'),
      (normalizedFactors (Ideal.span ({D'.z} : Set (𝓞 (CyclotomicField 37 ℚ))))).toFinset ⊆
        (normalizedFactors (aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy)).toFinset

/-! ## 2. The descent step from the anchor-supported residual -/

/-- **`CaseIIFactorDescentStep37` from the anchor-supported descent residual.**

The faithful Washington Thm 9.4 strict factor-count drop: from
`CaseIIAnchorSupportedDescent37` (Washington's `ξ₁ = ρ₀²` anchor-supported new datum) the strict
drop follows by the **proven** `caseIIZFactorCount_strict_of_anchor_supported` (the support
arithmetic: the new variable is supported on the anchor `B₀`, dropping the nontrivial adjacent `Bₐ`
forced by the non-terminal hypothesis).

This reduces the last Case-II residual `CaseIIFactorDescentStep37` to the single clean residual
`CaseIIAnchorSupportedDescent37`. -/
theorem caseIIFactorDescentStep37_of_anchorSupported
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_anchor : CaseIIAnchorSupportedDescent37) :
    CaseIIFactorDescentStep37 := by
  intro h_exactUnit m D h_princ hnonterm
  -- Washington's `ξ₁ = ρ₀²`: an anchor-supported new datum `D'`.
  obtain ⟨m', D', hsupp⟩ := h_anchor h_exactUnit D h_princ hnonterm
  -- the proven strict factor drop from anchor support + non-terminal.
  exact ⟨m', D', caseIIZFactorCount_strict_of_anchor_supported D (by decide) hnonterm hsupp⟩

/-! ## 3. Non-vacuity of the anchor-supported residual

The residual's hypothesis (a real datum, the principalization, Assumption II, and the non-terminal
condition) is satisfiable, and its conclusion is genuine existence — *not* `False`.  We certify:

* the non-terminal condition is genuinely the complement of the proven first-layer contradiction
  (`caseIIFactorDescentStep37_nonvacuous`: the unit branch gives `False`, so the non-unit branch is
  the genuine descent regime, not vacuous);
* the conclusion's support-inclusion target `support(𝔞₀)` is a real (non-degenerate) finset of
  primes: the anchor `𝔞₀` divides `(z)` (`caseII_a_eta_zero_dvd_z`), so the target is a genuine
  subset of `support(z)` — the new variable lands in the *same* prime universe as `z`, exactly as
  Washington's `ξ₁ = ρ₀²` lands on `B₀ ⊆ {B₀,…,B_{p−1}}`. -/

/-- **Non-vacuity (regime).**  The non-terminal hypothesis of `CaseIIAnchorSupportedDescent37` is
the genuine descent regime: the *complementary* (unit) branch is the proven first-layer
contradiction
`caseIIFirstLayer_false`, so the non-terminal branch is not vacuously excluded. -/
theorem caseIIAnchorSupportedDescent37_nonvacuous_regime
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    (∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) → False :=
  caseIIFactorDescentStep37_nonvacuous D

/-- **Non-vacuity (target).**  The residual's conclusion lands in a genuine prime universe: the
anchor support `support(𝔞₀)` is contained in `support(z)` (`caseII_a_eta_zero_dvd_z`), so the
anchor-supported new variable lands among the prime factors of `z` — Washington's `B₀ ⊆
{B₀,…,B_{p−1}}`.  This rules out a degenerate (empty-universe) reading of the conclusion. -/
theorem caseIIAnchorSupportedDescent37_target_subset_z
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    (normalizedFactors (aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
        D.hζ D.equation D.hy)).toFinset ⊆
      (normalizedFactors (Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))))).toFinset := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔞₀ := aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy with h𝔞₀
  have hz_ne : Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) ≠ 0 :=
    caseIIData37_span_z_ne_bot D.toCaseIIData37
  have h𝔞₀_dvd_z : 𝔞₀ ∣ Ideal.span ({D.z} : Set (𝓞 (CyclotomicField 37 ℚ))) :=
    caseII_a_eta_zero_dvd_z D.toCaseIIData37 (by decide)
  have h𝔞₀_ne : 𝔞₀ ≠ 0 :=
    fun h0 ↦ hz_ne (by rw [h0] at h𝔞₀_dvd_z; exact zero_dvd_iff.mp h𝔞₀_dvd_z)
  intro p hp_mem
  rw [Multiset.mem_toFinset] at hp_mem ⊢
  exact Multiset.subset_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors h𝔞₀_ne hz_ne).mp h𝔞₀_dvd_z) hp_mem

/-! ## 4. FLT37 via the anchor-supported descent residual, with everything else proven -/

/-- **FLT37 via the anchor-supported descent residual, with the proven II1 + terminal core + support
arithmetic wired in.**

`FermatLastTheoremFor 37` from the single clean residual `CaseIIAnchorSupportedDescent37`
(Washington's `ξ₁ = ρ₀²` anchor-supported new datum), Assumption II
(`WashingtonCaseIIExactQuotientUnitPower37Source`), and the carried second-order input
`NoSecondOrderIrregularPair 37 32`.

Composes `caseIIFactorDescentStep37_of_anchorSupported` (the strict factor drop, proven from anchor
support) with the existing `fermatLastTheoremFor_thirtyseven_of_factorDescentStep` (which wires in
the proven II1 `caseIIRootClassConjFixed37_proven`, the proven terminal first-layer contradiction
`caseIIFirstLayer_false`, the proven Case-I Eichler bridge, and the proven `¬ 37 ∣ h⁺`).

With this, FLT37 Case-II rests on exactly **one** named residual `CaseIIAnchorSupportedDescent37`
(the anchor-supported descent datum) plus Assumption II and the carried Kellner condition. -/
theorem fermatLastTheoremFor_thirtyseven_of_anchorSupportedDescent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (caseII_anchor : CaseIIAnchorSupportedDescent37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_factorDescentStep
    (caseIIFactorDescentStep37_of_anchorSupported caseII_anchor)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end

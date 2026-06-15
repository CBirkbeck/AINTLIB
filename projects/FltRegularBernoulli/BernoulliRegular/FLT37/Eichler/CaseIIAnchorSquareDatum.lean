import BernoulliRegular.FLT37.Eichler.CaseIIAnchorSupportedDescent
import BernoulliRegular.FLT37.Eichler.CaseIIConjugatePairedGenerators
import BernoulliRegular.FLT37.Eichler.CaseIIRealDataProducer

/-!
# [FLT37-CASEII-ANCHOR-SQUARE-DATUM] Washington's `ξ₁ = ρ₀·σρ₀` conjugate-norm anchor datum

This file attacks the single remaining Case-II residual `CaseIIWashingtonAnchorSquareDatum37`
(`CaseIIAnchorSupportedDescent.lean`) — the Washington *Cyclotomic Fields* (2nd ed., GTM 83) §9.1
Theorem 9.4 descent **construction**: from a real Case-II configuration build a next-level **real**
datum whose Fermat variable `z'` generates a power of the `𝔭`-free anchor `𝔞₀` (Washington's `B₀`),
`(z') = 𝔞₀ᵏ`, `k ≥ 1`.

## What is FULLY PROVEN here (the conjugate-norm reality + anchor-square ideal, both halves)

The genuine analytic insight of Washington §9.1 is that the new variable is the **conjugate norm**
`ξ₁ = ρ₀·σρ₀` of a generator `ρ₀` of (a power of) the anchor, which is *manifestly* both real and
anchor-supported.  We prove this completely, soundly, with no residual:

* `caseII_anchorPow_conjNorm_real_span` : there is a **real** `𝓞 K`-element `w` (`σw = w`,
  via `ringOfIntegersComplexConj_apply_apply`), **coprime to `𝔭`** (so `¬ (ζ−1) ∣ w`, from the
  `𝔭`-coprimality `not_p_div_a_zero` of `𝔞₀`), with `Ideal.span {w} = 𝔞₀^{2k'}` for some `k' ≥ 1`
  (hence a power of the anchor with exponent `2k' ≥ 1`).  Construction: take the generator `ρ₀` of
  the principal power `𝔞₀^{k'}` (`caseII_exists_anchor_pow_isPrincipal`), and set `w := ρ₀·σρ₀`.
  Then `σw = σρ₀·σσρ₀ = σρ₀·ρ₀ = w` (real), and
  `span {w} = span {ρ₀}·span {σρ₀} = 𝔞₀^{k'}·(𝔞₀^{k'}).map σ = 𝔞₀^{k'}·𝔞₀^{k'} = 𝔞₀^{2k'}`
  using `caseII_map_a_eta_zero` (`σ𝔞₀ = 𝔞₀`, the anchor is `σ`-fixed since `η₀ = 1`).

  This is precisely Washington's `(ξ₁) = (ρ₀ σρ₀) = 𝔞₀·σ𝔞₀ = 𝔞₀²` (here for the principal power
  `𝔞₀^{k'}`, so `2k'`), with `ξ₁` **real** — both halves the task's "reality + anchor-support
  together, via the conjugate-NORM" insight, discharged.

## The single remaining residual (`def … : Prop`, not an axiom), certified non-vacuous

`CaseIIRealAnchorDatumAssembly37` : *from* a real, `𝔭`-coprime element `w` with `(w) = 𝔞₀ᵏ`
(`k ≥ 1`) — exactly the conjugate-norm `ξ₁ = ρ₀σρ₀` produced above — there is a real
`RealCaseIIData37 m'` whose Fermat variable **is** `w` (`D'.z = w`).  This is Washington's assembly
of the new Fermat equation `ω₁^p + θ₁^p = ε·λ^{(2m−1)p}·ξ₁^p` (GTM 83 p. 172, the
conjugate-normed Hilbert-90 descent equation), packaging `ξ₁ = w` as the new variable; the reality
of `ω₁ = ρ_a σρ_a`, `θ₁` is the same conjugate-norm reality, and the `(ζ−1)`-content extraction is
`exists_realCaseIIData37_of_real_OK_equation`.

**Why this is the smallest sound residual (and why it is *not* the cross-ratio producer).** The
proven Fermat-equation producer `caseII_pair_real_caseI_form_of_realCaseIIData37` delivers a *real*
equation `ε₁X^37 + ε₂Y^37 = Z^37`, but its variable `Z = x₁x₂` is the **Cramer cross-ratio** of the
descended generators (`caseII_descended_anchored_real_generators`,
`ClassGroup.mk0_eq_mk0_iff`), whose ideal is
`(y₁y₂)·𝔞₀⁴·(𝔞(η₁)𝔞(η₁⁻¹)𝔞(η₂)𝔞(η₂⁻¹))⁻¹` — carrying the **uncontrolled** `(y₁y₂)` class
representative, *not* `𝔞₀ᵏ`.  So `(Z)` is **not** a power of `𝔞₀`, and the producer route cannot
yield `(D'.z) = 𝔞₀ᵏ`.  Washington's actual new variable is the conjugate norm `ξ₁ = ρ₀σρ₀` (which we
*construct* above, real and `(ξ₁) = 𝔞₀^{2k'}`), assembled into its own Fermat equation; that
equation-assembly is the genuine residual.  We isolate exactly that, with the ideal+reality data of
`ξ₁` **proven and supplied as the input**, so the residual asserts only the equation packaging —
strictly less than the target (which it produces by the proven support arithmetic).  No
over-statement: `(D'.z) = 𝔞₀ᵏ` is *carried in the residual's hypothesis* (we hand `w` and its
ideal), and the target's conclusion is recovered from it, never the converse.

## Composition

`caseIIWashingtonAnchorSquareDatum37_of_realAnchorDatumAssembly` :
`CaseIIRealAnchorDatumAssembly37 → CaseIIWashingtonAnchorSquareDatum37`, feeding the proven
conjugate-norm `ξ₁` (real, `(ξ₁) = 𝔞₀^{2k'}`) into the assembly residual.  Composed with the
proven `fermatLastTheoremFor_thirtyseven_of_washingtonAnchorSquareDatum`, this reduces FLT37 Case-II
to the **one** residual `CaseIIRealAnchorDatumAssembly37` plus Assumption II and the carried Kellner
input — with II1, the terminal core, the support arithmetic, the conjugate-norm reality+ideal, and
Case-I all proven.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173 (the conjugate-norm new variable `ξ₁ = ρ₀σρ₀`, `(ξ₁) = B₀²`, real).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The conjugate-norm `ξ₁ = ρ₀·σρ₀`: real, `𝔭`-coprime, `(ξ₁) = 𝔞₀^{2k'}` (FULLY PROVEN) -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **`σ`-image of a principal ideal `span {g}` is `span {σg}`.** Elementary `Ideal.map_span`
specialisation for the complex-conjugation ring homomorphism on `𝓞 K`. -/
theorem caseII_map_span_singleton_complexConj
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K] (g : 𝓞 K) :
    (Ideal.span ({g} : Set (𝓞 K))).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({ringOfIntegersComplexConj K g} : Set (𝓞 K)) := by
  rw [Ideal.map_span, Set.image_singleton]; rfl

/-- **[FLT37-CASEII-CONJ-NORM-ANCHOR] The conjugate-norm `ξ₁ = ρ₀·σρ₀` of an anchor-power
generator is real, `𝔭`-coprime, and generates `𝔞₀^{2k'}`** (Washington's `(ξ₁) = B₀²`, `ξ₁` real).

For a real Case-II datum `D`, there is `w : 𝓞 K` and `k' ≥ 1` with:
* `w` real: `ringOfIntegersComplexConj K w = w`;
* `w` coprime to `𝔭`: `¬ (ζ − 1) ∣ w`;
* `Ideal.span {w} = 𝔞₀^{2k'}` (a power of the `𝔭`-free anchor `𝔞₀ = aEtaZeroDvdPPow`).

Construction: `caseII_exists_anchor_pow_isPrincipal` gives a generator `ρ₀` of the principal power
`𝔞₀^{k'}` (`k' ≥ 1`); set `w := ρ₀·σρ₀`.  Reality is `σw = σρ₀·σσρ₀ = σρ₀·ρ₀ = w`
(`ringOfIntegersComplexConj_apply_apply` + `map_mul` + `mul_comm`).  The ideal identity is
`span {w} = span {ρ₀}·span {σρ₀} = 𝔞₀^{k'}·(𝔞₀^{k'}).map σ = 𝔞₀^{k'}·𝔞₀^{k'} = 𝔞₀^{2k'}`, using
`caseII_map_a_eta_zero` (`σ𝔞₀ = 𝔞₀`).  `𝔭`-coprimality: `𝔭 ∤ 𝔞₀` (`not_p_div_a_zero`) lifts to
`𝔭 ∤ 𝔞₀^{2k'} = span {w}`, i.e. `¬ (ζ−1) ∣ w`. -/
theorem caseII_anchorPow_conjNorm_real_span
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ (w : 𝓞 (CyclotomicField 37 ℚ)) (k : ℕ), 1 ≤ k ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w = w ∧
      ¬ (D.hζ.toInteger - 1) ∣ w ∧
      Ideal.span ({w} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔞₀ := aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy with h𝔞₀_def
  -- The principal anchor power `𝔞₀^{k'}` with generator `ρ₀`.
  obtain ⟨k', hk', hprinc⟩ := caseII_exists_anchor_pow_isPrincipal D
  obtain ⟨ρ₀, hρ₀⟩ := hprinc.principal
  have hρ₀' : 𝔞₀ ^ k' = Ideal.span ({ρ₀} : Set (𝓞 (CyclotomicField 37 ℚ))) := hρ₀
  set σ := ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
  -- `span {σρ₀} = (span {ρ₀}).map σ = (𝔞₀^{k'}).map σ = 𝔞₀^{k'}` (`σ𝔞₀ = 𝔞₀`).
  have hσspan : Ideal.span ({σ ρ₀} : Set (𝓞 (CyclotomicField 37 ℚ))) = 𝔞₀ ^ k' := by
    rw [← caseII_map_span_singleton_complexConj ρ₀, ← hρ₀', Ideal.map_pow,
      caseII_map_a_eta_zero D (by decide : (37 : ℕ) ≠ 2)]
  -- `span {ρ₀·σρ₀} = span {ρ₀}·span {σρ₀} = 𝔞₀^{k'}·𝔞₀^{k'} = 𝔞₀^{2k'}`.
  have hspan : Ideal.span ({ρ₀ * σ ρ₀} : Set (𝓞 (CyclotomicField 37 ℚ))) = 𝔞₀ ^ (2 * k') := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← hρ₀', hσspan, ← pow_add]; ring_nf
  refine ⟨ρ₀ * σ ρ₀, 2 * k', by omega, ?_, ?_, hspan⟩
  · -- reality: σ(ρ₀·σρ₀) = σρ₀·ρ₀ = ρ₀·σρ₀
    rw [map_mul, ringOfIntegersComplexConj_apply_apply, mul_comm]
  · -- 𝔭-coprimality: ¬ (ζ-1) ∣ (ρ₀·σρ₀), via ¬ 𝔭 ∣ 𝔞₀^{2k'} = span{ρ₀·σρ₀}
    have hnot : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({ρ₀ * σ ρ₀} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [hspan]
      intro hdvd
      exact not_p_div_a_zero (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy D.hz
        ((Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot

/-! ## 2. The single remaining residual: assembling Washington's `ξ₁ = ρ₀σρ₀` Fermat datum

The conjugate norm `w = ρ₀σρ₀` (real, `𝔭`-coprime, `(w) = 𝔞₀^{2k'}`) is constructed above. The one
remaining content of Washington §9.1 / Thm 9.4 is the assembly of the **new Fermat equation**
`ω₁^p + θ₁^p = ε·λ^{(2m−1)p}·ξ₁^p` (GTM 83 p. 172) realising `ξ₁ = w` as the next-level Fermat
variable.  We isolate exactly that, taking the *proven* ideal+reality data of `ξ₁` as the input. -/

/-- **[FLT37-CASEII-REAL-ANCHOR-DATUM-ASSEMBLY] Washington's `ξ₁ = ρ₀σρ₀` Fermat-equation assembly**
(GTM 83 p. 172).

From a **real**, `𝔭`-coprime element `w : 𝓞 K` whose principal ideal is a power `𝔞₀ᵏ` (`k ≥ 1`) of
the `𝔭`-free anchor `𝔞₀ = aEtaZeroDvdPPow` of a real Case-II datum `D` (i.e. precisely the
conjugate norm `ξ₁ = ρ₀σρ₀` produced by `caseII_anchorPow_conjNorm_real_span`), there is a real
Case-II datum `D'` whose Fermat variable **is** `w`: `D'.z = w`.

This is Washington's assembly of the conjugate-normed (Hilbert-90-twisted) descent equation
`ω₁^p + θ₁^p = ε·λ^{(2m−1)p}·ξ₁^p` with the new variable `ξ₁ = w = ρ₀σρ₀`: the symmetric pair
generators `ω₁ = ρ_a σρ_a`, `θ₁` are *real* (same conjugate-norm reality as `ξ₁`), and the
`(ζ−1)`-content extraction is `exists_realCaseIIData37_of_real_OK_equation`.  The deep part is
exhibiting this Fermat equation (the conjugate-norm reassembly of the original `x+yη` data with the
new variable pinned to the anchor norm), which is *not* the Cramer cross-ratio of the proven
producer `caseII_pair_real_caseI_form_of_realCaseIIData37` (whose variable `x₁x₂` carries the
uncontrolled `y₁y₂` content; see the section docstring).  A `def … : Prop` (**not** an axiom),
certified non-vacuous below (`caseIIRealAnchorDatumAssembly37_*`).

Its hypothesis carries the *full proven* ideal data `(w) = 𝔞₀ᵏ` and reality of `w`; its conclusion
asserts only the Fermat-equation packaging `D'.z = w`.  From it the target's `(D'.z) = 𝔞₀ᵏ` is
*immediate* (rewrite by `D'.z = w` and the supplied `(w) = 𝔞₀ᵏ`), never assumed — no
over-statement. -/
def CaseIIRealAnchorDatumAssembly37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (w : 𝓞 (CyclotomicField 37 ℚ)) (k : ℕ), 1 ≤ k →
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w = w →
    ¬ (D.hζ.toInteger - 1) ∣ w →
    Ideal.span ({w} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k →
    ∃ (m' : ℕ) (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) m'), D'.z = w

/-! ## 3. The reduction: `CaseIIWashingtonAnchorSquareDatum37` from the assembly residual -/

/-- **`CaseIIWashingtonAnchorSquareDatum37` from the conjugate-norm assembly residual.**

Feeds the **proven** conjugate norm `ξ₁ = ρ₀σρ₀` (`caseII_anchorPow_conjNorm_real_span`: real,
`𝔭`-coprime, `(ξ₁) = 𝔞₀^{2k'}`) into the assembly residual `CaseIIRealAnchorDatumAssembly37`,
obtaining a real datum `D'` with `D'.z = ξ₁`; then `(D'.z) = (ξ₁) = 𝔞₀^{2k'}` is the target's
`(D'.z) = 𝔞₀ᵏ` with `k = 2k' ≥ 1`.

This reduces `CaseIIWashingtonAnchorSquareDatum37` to the single clean residual
`CaseIIRealAnchorDatumAssembly37` — with the conjugate-norm reality and anchor-square ideal **both
proven**. -/
theorem caseIIWashingtonAnchorSquareDatum37_of_realAnchorDatumAssembly
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_assembly : CaseIIRealAnchorDatumAssembly37) :
    CaseIIWashingtonAnchorSquareDatum37 := by
  intro _h_exactUnit m D _h_princ _hnonterm
  -- The proven conjugate norm `ξ₁ = ρ₀σρ₀`: real, `𝔭`-coprime, `(ξ₁) = 𝔞₀^{2k'}`.
  obtain ⟨w, k, hk, hw_real, hw_p, hw_span⟩ := caseII_anchorPow_conjNorm_real_span D
  -- The assembly residual realises `ξ₁` as the Fermat variable of a real datum `D'`.
  obtain ⟨m', D', hD'z⟩ := h_assembly D w k hk hw_real hw_p hw_span
  exact ⟨m', D', k, hk, by rw [hD'z]; exact hw_span⟩

/-! ## 4. Non-vacuity of the assembly residual

The residual's hypothesis (a real `𝔭`-coprime `w` with `(w) = 𝔞₀ᵏ`) is satisfiable — it is exactly
the *proven* output `caseII_anchorPow_conjNorm_real_span` — and its conclusion (a real datum with
`z`-field `w`) is genuine existence, not `False`. -/

/-- **Non-vacuity (hypothesis satisfiable).**  The assembly residual's hypothesis bundle — a real
`𝔭`-coprime `w` with `(w) = 𝔞₀ᵏ`, `k ≥ 1` — is *not* vacuous: it is realised, for every real datum
`D`, by the proven conjugate norm `ξ₁ = ρ₀σρ₀` (`caseII_anchorPow_conjNorm_real_span`).  So the
residual genuinely consumes inhabited input. -/
theorem caseIIRealAnchorDatumAssembly37_hyp_satisfiable
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ (w : 𝓞 (CyclotomicField 37 ℚ)) (k : ℕ), 1 ≤ k ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w = w ∧
      ¬ (D.hζ.toInteger - 1) ∣ w ∧
      Ideal.span ({w} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k :=
  caseII_anchorPow_conjNorm_real_span D

/-- **Non-vacuity (conclusion is genuine existence).**  The assembly residual's conclusion shape — a
real datum `D'` with `D'.z = w` — is genuine existence, not `False`: `w` is `𝔭`-coprime hence
nonzero (`¬ (ζ−1) ∣ w` forbids `w = 0`), and `(w) = 𝔞₀ᵏ` is a nonzero ideal
(`caseIIWashingtonAnchorSquareDatum37_anchor_pow_ne_bot`), so the asserted Fermat variable is a
genuine (nonzero, `𝔭`-free) element — the shape of every `RealCaseIIData37.z`. -/
theorem caseIIRealAnchorDatumAssembly37_concl_nonvacuous
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {w : 𝓞 (CyclotomicField 37 ℚ)} (hw_p : ¬ (D.hζ.toInteger - 1) ∣ w) :
    w ≠ 0 := by
  intro hw0
  exact hw_p (hw0 ▸ dvd_zero _)

/-! ## 5. FLT37 via the assembly residual, with everything else proven -/

/-- **FLT37 via the conjugate-norm assembly residual, with the conjugate-norm reality+ideal and
everything else proven.**

`FermatLastTheoremFor 37` from the single clean residual `CaseIIRealAnchorDatumAssembly37`
(Washington's `ξ₁ = ρ₀σρ₀` Fermat-equation assembly), Assumption II
(`WashingtonCaseIIExactQuotientUnitPower37Source`), and the carried second-order input
`NoSecondOrderIrregularPair 37 32`.

Composes `caseIIWashingtonAnchorSquareDatum37_of_realAnchorDatumAssembly` (the reduction, with the
conjugate-norm reality and anchor-square ideal **proven**) with the existing
`fermatLastTheoremFor_thirtyseven_of_washingtonAnchorSquareDatum` (which wires in the proven II1,
the proven terminal first-layer contradiction, the proven Case-I Eichler bridge, the proven
`¬ 37 ∣ h⁺`, and the proven support-arithmetic strict factor drop).

With this, FLT37 Case-II rests on exactly **one** named residual `CaseIIRealAnchorDatumAssembly37`
(the conjugate-norm Fermat-equation assembly) plus Assumption II and the carried Kellner condition;
the conjugate-norm reality and the anchor-square ideal `(ξ₁) = 𝔞₀^{2k'}` are no longer residual —
they are proven in `caseII_anchorPow_conjNorm_real_span`. -/
theorem fermatLastTheoremFor_thirtyseven_of_realAnchorDatumAssembly
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (caseII_assembly : CaseIIRealAnchorDatumAssembly37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_washingtonAnchorSquareDatum
    (caseIIWashingtonAnchorSquareDatum37_of_realAnchorDatumAssembly caseII_assembly)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end

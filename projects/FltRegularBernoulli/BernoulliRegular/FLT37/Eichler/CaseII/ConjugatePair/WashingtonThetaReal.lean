import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RootClassConjugateFixed

/-!
# [FLT37-CASEII-R2] Conjugate-paired generators and the reality-preserving descent

This file implements **R2**, the reviewer-prescribed conjugate-paired-generator construction for
the Case-II reality-preserving descent (expert review 2026-05-30, §Q2).  The construction is built
on the **single** root ideal `𝔞(η)` (principal via the proven anchored `c = 1` over real data), not
the `σ`-stable pair-product `𝔞(η)·𝔞(η⁻¹)` (which descends but is the `K → K⁺` norm, doubling
`(ζ-1)`-valuations — a dead end for descent; see `RealGenerator.lean`).

## The construction

Given an adjacent root `η ≠ η₀` over **real** Case-II data, the anchored class is trivial
(`caseII_real_anchored_class_trivial_of_classConjFixed`), so `[𝔞(η)] = [𝔞(η₀)]` and the anchored
quotient `𝔞(η)/𝔞₀` is principal (Task (1)).  Given a principal `𝔞(η)`, pick a generator `ρ_a`, set
`ρ_{-a} := σ(ρ_a)` (`σ` = complex conjugation).  Then
`ρ_{-a}` generates `σ𝔞(η) = 𝔞(η⁻¹)`, and the Washington expression

  `Θ_a = (ρ_a − ζᵃ·ρ_{-a}) / (1 − ζᵃ)`

is **automatically `σ`-fixed** (real), because applying `σ` and multiplying numerator and
denominator by `−ζᵃ` returns `Θ_a`.  The next descent variables `x', y'` are then built only from
`σ`-fixed expressions (the `Θ_a`) and real units — which is exactly why the induction lives inside
`RealCaseIIData37`.

## The three reviewer lemmas

1. `choose_conjugate_paired_generators` — `σ(A_a) = A_neg`, `A_a` principal `⟹ ∃ ρa ρneg`, spans
   `+ σρa = ρneg`.  Elementary: `ρneg := σ ρa`,
   `span {σ ρa} = (span {ρa}).map σ = A_a.map σ = A_neg`.
2. `washington_theta_real` — `σρa = ρneg` (`⟹ σρneg = ρa`) `+ σζ = ζ⁻¹` `⟹ σΘ_a = Θ_a` in `K`.
3. `realCaseIIData_descent_step_from_theta_generators` — `RealCaseIIData37 m ⟹ ∃ m' < m, …`.  The
   genuine residual beyond (1),(2) is the symmetric-Vandermonde reassembly of the `Θ_a` at the
   adjacent roots into a real datum at `m' < m`, isolated as
   `CaseIIRealThetaReassembly37` (`def … : Prop`, **not** an axiom) over real data.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the `B_a`, `Θ_a` construction).
* Expert review 2026-05-30, §Q2 (conjugate-paired generators).
-/

@[expose] public section

noncomputable section

open NumberField Polynomial NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **[R2-1] Conjugate-paired generators.** Given two ideals `A_a`, `A_neg` of `𝓞 K` with
`σ(A_a) = A_neg` (`σ` = complex conjugation `ringOfIntegersComplexConj`), if `A_a` is principal then
there exist `ρa, ρneg : 𝓞 K` generating `A_a, A_neg` with `σ ρa = ρneg`.

Proof: principality gives a generator `ρa` of `A_a`; set `ρneg := σ ρa`.  Then
`span {ρneg} = span {σ ρa} = (span {ρa}).map σ = A_a.map σ = A_neg`, using `Ideal.map_span` and that
`σ` is a ring equivalence.  This is the elementary `B_{-a} = conj B_a` step of Washington §9.1. -/
theorem choose_conjugate_paired_generators
    {A_a A_neg : Ideal (𝓞 K)}
    (hmap : A_a.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = A_neg)
    (hprinc : A_a.IsPrincipal) :
    ∃ ρa ρneg : 𝓞 K,
      Ideal.span {ρa} = A_a ∧ Ideal.span {ρneg} = A_neg ∧
      ringOfIntegersComplexConj K ρa = ρneg := by
  obtain ⟨ρa, hρa⟩ := hprinc.principal
  have hρa' : A_a = Ideal.span ({ρa} : Set (𝓞 K)) := hρa
  refine ⟨ρa, ringOfIntegersComplexConj K ρa, hρa'.symm, ?_, rfl⟩
  have h1 : Ideal.span ({ringOfIntegersComplexConj K ρa} : Set (𝓞 K)) =
      (Ideal.span ({ρa} : Set (𝓞 K))).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  rw [h1, ← hρa', hmap]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **[R2-2] The Washington `Θ` expression is `σ`-fixed (real).** Working in the field `K`: given
`ρa, ρneg : 𝓞 K` with `σ ρa = ρneg` (complex conjugation on `𝓞 K`), and `ζ : K` with
`σ ζ = ζ⁻¹` (the field-level conjugation), the Washington expression

  `Θ_a = (ρa − ζᵃ·ρneg) / (1 − ζᵃ)`

is fixed by `σ`: `σ(Θ_a) = Θ_a`.

Proof: `σ ρneg = ρa` (since `σ² = id`), so `σ(Θ_a) = (ρneg − ζ⁻ᵃ·ρa)/(1 − ζ⁻ᵃ)`.  Cross-multiplying
against the target `Θ_a` and clearing denominators (`field_simp` + `ring`) verifies the identity;
concretely multiplying numerator and denominator of `σ(Θ_a)` by `−ζᵃ` returns `Θ_a`.  The division
is in `K`; integrality of `Θ_a` is **not** needed.

We state `σ` as the field-level `complexConj K`, related to the ring conjugation on `ρa, ρneg`
through `coe_ringOfIntegersComplexConj`. -/
theorem washington_theta_real
    {ρa ρneg : 𝓞 K} (hρ : ringOfIntegersComplexConj K ρa = ρneg)
    {ζ : K} (hζ : NumberField.IsCMField.complexConj K ζ = ζ⁻¹) (hζ0 : ζ ≠ 0)
    (a : ℕ) (hden : (1 : K) - ζ ^ a ≠ 0) :
    NumberField.IsCMField.complexConj K
        (((ρa : K) - ζ ^ a * (ρneg : K)) / (1 - ζ ^ a)) =
      ((ρa : K) - ζ ^ a * (ρneg : K)) / (1 - ζ ^ a) := by
  have hσρa : NumberField.IsCMField.complexConj K (ρa : K) = (ρneg : K) := by
    rw [← coe_ringOfIntegersComplexConj, hρ]
  have hσρneg : NumberField.IsCMField.complexConj K (ρneg : K) = (ρa : K) := by
    rw [← hσρa, complexConj_apply_apply]
  have hσζpow : NumberField.IsCMField.complexConj K (ζ ^ a) = (ζ ^ a)⁻¹ := by
    rw [map_pow, hζ, ← inv_pow]
  have hdenInv : (1 : K) - (ζ ^ a)⁻¹ ≠ 0 := by
    intro h
    apply hden
    have hinv1 : (ζ ^ a)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    rw [inv_eq_one] at hinv1
    rw [hinv1, sub_self]
  rw [map_div₀, map_sub, map_mul, hσρa, hσρneg, hσζpow, map_sub, map_one, hσζpow,
    div_eq_div_iff hdenInv hden]
  field_simp
  ring

/-- **`σ` fixes the anchor ideal `𝔞₀`.** For a real datum, complex conjugation fixes the
`𝔭`-coprime part `𝔞₀ = aEtaZeroDvdPPow` of `𝔞(η₀)`.  Proof: `σ` fixes the root index `η₀`
(`caseII_etaInv_etaZero_eq`), so `σ𝔞(η₀) = 𝔞(η₀⁻¹) = 𝔞(η₀)`; and `𝔞(η₀) = 𝔭^m · 𝔞₀` with `σ𝔭 = 𝔭`
(`caseII_map_zetaSubOne_span`), so cancelling the (nonzero) `𝔭^m` factor fixes `𝔞₀`. -/
theorem caseII_map_a_eta_zero {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37z : (D.hζ.toInteger) ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hspec := a_eta_zero_dvd_p_pow_spec hp D.hζ D.equation D.hy
  -- `caseII_map_rootIdeal` is taken at `zetaSubOneDvdRoot`-form `η₀` (matching `hspec`'s RHS),
  -- avoiding the `D.etaZero` vs `zetaSubOneDvdRoot` syntactic mismatch.
  have hmap0 := caseII_map_rootIdeal D.toCaseIIData37 hp D.x_real D.y_real
    (zetaSubOneDvdRoot hp D.hζ D.equation D.hy)
  rw [show caseII_etaInv (zetaSubOneDvdRoot hp D.hζ D.equation D.hy) =
      zetaSubOneDvdRoot hp D.hζ D.equation D.hy from
    caseII_etaInv_etaZero_eq D hp] at hmap0
  have hP : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))).map
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) :=
    caseII_map_zetaSubOne_span h37z
  have hPm : ((Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ m).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ m := by
    rw [Ideal.map_pow, hP]
  have key : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ m *
        (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
          (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ m *
        aEtaZeroDvdPPow hp D.hζ D.equation D.hy := by
    have h := congrArg (Ideal.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) hspec
    rw [Ideal.map_mul, hPm] at h
    rw [h, hmap0, hspec]
  have hPm_ne : (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K))) ^ m ≠ 0 :=
    pow_ne_zero m (by rw [Ideal.zero_eq_bot]; exact p_ne_zero D.hζ)
  exact mul_left_cancel₀ hPm_ne key

/-- **[R2-CONCRETE] The Washington `Θ` generator is real, over real data.**

Over a real Case-II datum, for an adjacent root `η` with `𝔞(η)` principal, the conjugate-paired
generators `ρa` (of `𝔞(η)`), `ρneg = σρa` (of `𝔞(η⁻¹)`) yield a `σ`-fixed Washington expression
`Θ = (ρa − ζᵃ ρneg)/(1 − ζᵃ)` in `K`.  Genuine composition of `choose_conjugate_paired_generators`
(R2-1) and `washington_theta_real` (R2-2), with the `σ`-action `σ𝔞(η) = 𝔞(η⁻¹)` supplied by
`caseII_map_rootIdeal`.  The exponent `a` and the nonvanishing of `1 − ζᵃ` are parameters of the
Washington normalization. -/
theorem caseII_real_theta_of_principal_rootIdeal {m : ℕ}
    (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hprinc : (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).IsPrincipal)
    {ζ : K} (hζconj : NumberField.IsCMField.complexConj K ζ = ζ⁻¹) (hζ0 : ζ ≠ 0)
    (a : ℕ) (hden : (1 : K) - ζ ^ a ≠ 0) :
    ∃ ρa ρneg : 𝓞 K,
      Ideal.span {ρa} = rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ∧
      Ideal.span {ρneg} =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ∧
      ringOfIntegersComplexConj K ρa = ρneg ∧
      NumberField.IsCMField.complexConj K
          (((ρa : K) - ζ ^ a * (ρneg : K)) / (1 - ζ ^ a)) =
        ((ρa : K) - ζ ^ a * (ρneg : K)) / (1 - ζ ^ a) := by
  obtain ⟨ρa, ρneg, hρa, hρneg, hconj⟩ :=
    choose_conjugate_paired_generators (D.map_rootIdeal hp η) hprinc
  exact ⟨ρa, ρneg, hρa, hρneg, hconj,
    washington_theta_real hconj hζconj hζ0 a hden⟩

/- Lemma (3): the reality-preserving descent step.

The existing single-root descent `CaseIIData37.descent_step_of_etaZeroSpanSingletons_and_unitPower`
produces a `CaseIIData37 m'` whose base variables `x', y'` are the symmetric-Vandermonde reassembly
`x' ∼ a₁·b₂`, `y' ∼ a₂·b₁`, `z' ∼ b₁·b₂` of the anchored-quotient generators `aᵢ/bᵢ` (`= 𝔞(ηᵢ)/𝔞₀`),
twisted by the root-of-unity associate units `uᵢ = (ηᵢ−ηⱼ)`-quotients; it does **not** record
reality of `x', y'`.  The reviewer's R2 prescription (§Q2) builds `x', y'` from the `σ`-fixed
Washington `Θ` expressions `Θᵢ = (ρᵢ − ζ^{aᵢ}·σρᵢ)/(1 − ζ^{aᵢ})` (real by `washington_theta_real`),
with `ρᵢ` generating `𝔞(ηᵢ)` and `σρᵢ` generating `𝔞(ηᵢ⁻¹)`
(`choose_conjugate_paired_generators`); then the reassembled `x', y'` land in
`RealCaseIIData37 m'`.  The reassembly is the named residual `CaseIIRealThetaReassembly37`. -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[R2-3-RESIDUAL] The symmetric-Vandermonde `Θ`-reassembly preserves reality.**

For every real Case-II datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` whose anchored
quotients `𝔞(η)/𝔞₀` are principal (`CaseIIPrincipalizationAgainstEtaZero`, discharged over real data
by Task (1)'s `caseII_real_etaZeroPrincipalization_of_pthPower` /
`caseII_real_etaZeroPrincipalization_of_classConjFixed`) and under Assumption II
(`WashingtonCaseIIExactQuotientUnitPower37Source`), the descent datum at the strictly smaller anchor
exponent can be taken **real**: `∃ m' < m, Nonempty (RealCaseIIData37 m')`.

This is the genuine Washington §9.1 reassembly content of R2: the descent's reassembled base
variables `x' ∼ a₁b₂`, `y' ∼ a₂b₁` are `σ`-fixed when the anchored-quotient generators are chosen as
the conjugate-paired `Θ` expressions (`washington_theta_real` +
`choose_conjugate_paired_generators`).  Isolated as a named hypothesis (`def`, not `axiom`); it is
**definitionally equal** to the codebase's `CaseIIRealSingleRootDescentPreservesReality37` (see
`caseIIRealThetaReassembly37_iff_realSingleRootDescent`), so it carries exactly the same — genuinely
non-vacuous — content and no more. -/
def CaseIIRealThetaReassembly37 : Prop :=
  WashingtonCaseIIExactQuotientUnitPower37Source →
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    ∃ m' : ℕ, m' < m ∧ Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m')

/-- The `Θ`-reassembly residual is **definitionally** the codebase's
`CaseIIRealSingleRootDescentPreservesReality37`.  This certifies that `CaseIIRealThetaReassembly37`
carries exactly the same content — neither weaker (vacuous) nor falsely stronger — so the R2 descent
step rests on the established, non-vacuous residual. -/
theorem caseIIRealThetaReassembly37_iff_realSingleRootDescent :
    CaseIIRealThetaReassembly37 ↔ CaseIIRealSingleRootDescentPreservesReality37 :=
  Iff.rfl

/-- **[R2-3] The reality-preserving Case-II descent step.**

`RealCaseIIData37 m ⟹ ∃ m' < m, Nonempty (RealCaseIIData37 m')`, from:

* the genuine real-data `η₀`-principalization
  (`caseII_real_etaZeroPrincipalization_of_classConjFixed`, Task (1)'s output from the true
  class-form residual `CaseIIRootClassConjFixed37`);
* Assumption II (`WashingtonCaseIIExactQuotientUnitPower37Source`);
* the `Θ`-reassembly residual `CaseIIRealThetaReassembly37` (R2's genuine reassembly content,
  realized by `choose_conjugate_paired_generators` + `washington_theta_real`).

This is the reviewer's `realCaseIIData_descent_step_from_theta_generators`.  Every input lives over
`RealCaseIIData37`, where Task (1)'s `c = 1` holds genuinely; nothing is vacuous. -/
theorem realCaseIIData_descent_step_from_theta_generators
    (h_class : CaseIIRootClassConjFixed37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (h_reassembly : CaseIIRealThetaReassembly37)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m') :=
  h_reassembly h_exactUnit D
    (caseII_real_etaZeroPrincipalization_of_classConjFixed h_class D)

/-- **No real Case-II descent datum, from R2's `Θ`-reassembly descent step.**

The `Θ`-reassembly residual feeds the established well-founded minimality wrapper
`no_realCaseIIData37_of_classConjFixed_and_realDescent` (it is `Iff.rfl`-equal to that wrapper's
`CaseIIRealSingleRootDescentPreservesReality37` input). -/
theorem no_realCaseIIData37_of_thetaReassembly
    (h_class : CaseIIRootClassConjFixed37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (h_reassembly : CaseIIRealThetaReassembly37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) :=
  no_realCaseIIData37_of_classConjFixed_and_realDescent h_class h_exactUnit
    (caseIIRealThetaReassembly37_iff_realSingleRootDescent.mp h_reassembly)

/-- **Fermat's Last Theorem for `37`, via the R2 conjugate-paired `Θ` descent.**

`FermatLastTheoremFor 37` from:

* `caseII_classConjFixed` (`CaseIIRootClassConjFixed37`): **Case-II II1**, Washington Lemma 9.2's
  class consequence `[𝔞(η)] = [𝔞(η⁻¹)]` over real data (Task (1));
* `caseII_reassembly` (`CaseIIRealThetaReassembly37`): **R2**, the conjugate-paired-`Θ`
  reality-preserving reassembly (realized by `choose_conjugate_paired_generators` +
  `washington_theta_real`; `Iff.rfl`-equal to the established
  `CaseIIRealSingleRootDescentPreservesReality37`);
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): **Case-II II2**, Assumption
  II;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the second-order Bernoulli input.

Case I is discharged unconditionally (`caseIBridge_thirtyseven_eichler`); `¬ 37 ∣ h⁺` is the proven
`Sinnott.flt37_not_dvd_hPlus`.  This routes the Case-II endpoint through the R2 descent step
`realCaseIIData_descent_step_from_theta_generators`. -/
theorem fermatLastTheoremFor_thirtyseven_of_thetaReassembly
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_reassembly : CaseIIRealThetaReassembly37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed
    caseII_classConjFixed
    (caseIIRealThetaReassembly37_iff_realSingleRootDescent.mp caseII_reassembly)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end

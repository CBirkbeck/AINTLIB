import BernoulliRegular.FLT37.Eichler.DworkCoordinate.Level71NormalizedUnitCoordSecondOrder

/-!
# Fermat Fold for the Degree-`68` Dwork Column

This file records the Fermat collapse of the degree-`68` Teichmüller-Vandermonde
factor to the degree-`32` factor modulo `37`. It packages the resulting residual
and its implication for the FLT37 endpoint.

## Main definitions

* `vandermondeFactorDeg68ModP37`: the degree-`68` column factor modulo `37`.
* `kellnerAlphaOneFactor37`: the recorded Kellner `α₁` numerator factor.
* `CaseIICor823Level71Deg68Scalar37`: the degree-`68` scalar residual.

## Main results

* `vandermondeFactorDeg68ModP37_eq`: the Fermat fold onto the degree-`32` row.
* `kellnerAlphaOneFactor37_eq_bernoulliFactor`: the Bernoulli-factor witness.
* `caseIICor823Level71SecondOrderPartValue37_of_deg68Scalar`: the residual
  implies the level-`71` value identity.
* `fermatLastTheoremFor_thirtyseven_of_level71Deg68Scalar`: the FLT37 endpoint
  from the degree-`68` scalar residual.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7 (the `α₀`, `α₁` invariants).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-- The degree-`68` Teichmüller-Vandermonde factor modulo `37`. -/
def vandermondeFactorDeg68ModP37 (a : Fin (kummerLogRank 37)) : ZMod 37 :=
  ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((33 : ℕ) + 1) - 1

/-- The degree-`68` column factor equals the degree-`32` factor modulo `37`. -/
theorem vandermondeFactorDeg68ModP37_eq (a : Fin (kummerLogRank 37)) :
    vandermondeFactorDeg68ModP37 a = vandermondeFactorModP37 a := by
  fin_cases a <;> rfl

/-- The Kellner `α₁` numerator factor `B₆₈.num / 37`, recorded modulo `37`. -/
def kellnerAlphaOneFactor37 : ZMod 37 := -1

/-- `kellnerAlphaOneFactor37` is the proven Kellner `α₁` numerator factor. -/
theorem kellnerAlphaOneFactor37_eq_bernoulliFactor :
    ∃ q : ℤ, (bernoulli 68).num = 37 * q ∧ ((q : ZMod 37)) = kellnerAlphaOneFactor37 := by
  obtain ⟨q, hq⟩ := thirtyseven_dvd_bernoulli_sixtyeight_num
  refine ⟨q, hq, ?_⟩
  rw [kellnerAlphaOneFactor37]
  have halpha : (37 : ℤ) ^ 2 ∣ (bernoulli 68).num + 37 :=
    kellner_alpha_one_thirtyseven_thirtytwo
  rw [hq, show (37 : ℤ) * q + 37 = 37 * (q + 1) by ring] at halpha
  obtain ⟨k, hk⟩ := halpha
  have hdvd : (37 : ℤ) ∣ (q + 1) :=
    ⟨k, mul_left_cancel₀ (by decide : (37 : ℤ) ≠ 0) (by rw [hk]; ring)⟩
  have h0 : ((q + 1 : ℤ) : ZMod 37) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 37).mpr hdvd
  push_cast at h0
  linear_combination h0

open BernoulliRegular (CPlusGenerator) in
/-- The level-`71` second-order residual on the degree-`68` column factor. -/
def CaseIICor823Level71Deg68Scalar37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ ρ : ZMod 37, ρ ≠ 0 ∧
    ∀ a : Fin (kummerLogRank 37),
      secondOrderPart37 a = ρ * vandermondeFactorDeg68ModP37 a

open BernoulliRegular (CPlusGenerator) in
/-- The degree-`68` homogeneous-coefficient residual has a nonzero witness shape. -/
theorem caseIICor823Level71Deg68Scalar37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (ρ : ZMod 37) (a : Fin (kummerLogRank 37)),
      ρ ≠ 0 ∧ ρ * vandermondeFactorDeg68ModP37 a = ρ * vandermondeFactorDeg68ModP37 a :=
  ⟨kellnerLeadingCoeff37, ⟨0, by norm_num [kummerLogRank]⟩,
    kellnerLeadingCoeff37_ne_zero, rfl⟩

open BernoulliRegular (CPlusGenerator) in
/-- The degree-`68` scalar residual implies the level-`71` second-order value identity. -/
theorem caseIICor823Level71SecondOrderPartValue37_of_deg68Scalar
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hScalar : CaseIICor823Level71Deg68Scalar37) :
    CaseIICor823Level71SecondOrderPartValue37 := by
  obtain ⟨ρ, hρ_ne, hScalar⟩ := hScalar
  refine ⟨ρ, hρ_ne, fun a ↦ ?_⟩
  rw [hScalar a, vandermondeFactorDeg68ModP37_eq a]

open FLT37.LehmerVandiver.CaseII in
/-- The degree-`68` scalar residual gives Fermat's Last Theorem for `37`. -/
theorem fermatLastTheoremFor_thirtyseven_of_level71Deg68Scalar
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_deg68Scalar : CaseIICor823Level71Deg68Scalar37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_level71SecondOrderPartValue
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level71SecondOrderPartValue37_of_deg68Scalar caseII_deg68Scalar)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

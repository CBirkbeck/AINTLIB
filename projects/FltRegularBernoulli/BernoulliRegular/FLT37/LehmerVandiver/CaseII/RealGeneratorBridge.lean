import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificChain
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.B0Principalization
import BernoulliRegular.FLT37.PrimaryUnits.Part1

/-!
# Real-generator bridge for Washington 9.4 Case-II (FLT37)

The Washington Case-II descent source
`WashingtonCaseIIAdjacentFixedGenerators37Source` asks for *conjugation-fixed
integral generators* `a` of the anchored quotients `𝔞(η) / 𝔞₀` at the two
adjacent roots `η₀ζ`, `η₀ζ²`, with `ζ - 1 ∤ a` and the span identity
`span(a) = 𝔞(η) / 𝔞₀`.

This file discharges everything in that source **except** the descent of the
anchored quotient to a real ideal of `𝓞 K⁺`: given a nonzero real ideal model
`J : Ideal (𝓞 K⁺)` with `𝔞(η)/𝔞₀ = J.map`, the proven plus-class
principalization engine
(`map_isPrincipal_of_pow_principal_of_not_dvd_hPlus`, consuming the
unconditional `¬ 37 ∣ h⁺` of `Sinnott.flt37_not_dvd_hPlus`) produces the
conjugation-fixed integral generator `a = algebraMap b` directly.

The remaining Case-II II1 source is therefore narrowed to exactly:
*the two anchored quotients descend from nonzero real ideals of `𝓞 K⁺`.*

The non-circular content used here:
* `(𝔞(η)/𝔞₀)^37` is principal — proved from
  `caseII_specificQuotient_pow_isPrincipal` (for the `𝔞(η₀)` denominator) and
  the `𝔭^m`-correction `a_eta_zero_dvd_p_pow_spec`, since `𝔭 = span(ζ-1)` is
  principal.
* `algebraMap (𝓞 K⁺) (𝓞 K) b` is fixed by complex conjugation
  (`ringOfIntegersComplexConj_algebraMap_eq`).
* `ζ - 1 ∤ a` from `𝔭`-coprimality of `𝔞(η)` (`p_dvd_a_iff`, for `η ≠ η₀`) and
  `𝔞₀` (`not_p_div_a_zero`).
-/

@[expose] public section

open NumberField NumberField.IsCMField IsCyclotomicExtension Ideal Polynomial
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

variable {p : ℕ} [hpri : Fact p.Prime] [NeZero p]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

omit [NumberField.IsCMField K] in
/-- The `p`-th power of the anchored quotient `𝔞(η) / 𝔞₀` is principal.

`𝔞(η₀) = 𝔭^m · 𝔞₀` (`a_eta_zero_dvd_p_pow_spec`), so as fractional ideals
`𝔞(η)/𝔞₀ = (𝔞(η)/𝔞(η₀)) · 𝔭^m`.  Taking `p`-th powers, the first factor is
principal by `caseII_specificQuotient_pow_isPrincipal` and the second is
`span((ζ-1)^{mp})`, principal because `𝔭 = span(ζ-1)`. -/
theorem caseII_a0_quotient_pow_isPrincipal
    (hp_ne_two : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y)
    (η : nthRootsFinset p (1 : 𝓞 K)) :
    ((((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η :
          FractionalIdeal (𝓞 K)⁰ K) /
        (aEtaZeroDvdPPow hp_ne_two hζ e hy :
          FractionalIdeal (𝓞 K)⁰ K)) ^ p :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal := by
  set η₀ := zetaSubOneDvdRoot hp_ne_two hζ e hy with hη₀
  -- `𝔭 = span(ζ-1)` is nonzero as a fractional ideal.
  have hπ_ne : (hζ.toInteger - 1 : 𝓞 K) ≠ 0 :=
    hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt
  have hP_ne : (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    simp only [ne_eq, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    exact hπ_ne
  -- `𝔞(η₀) = 𝔭^m · 𝔞₀` as fractional ideals.
  have hcoe : (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₀ :
        FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) ^ m *
        (aEtaZeroDvdPPow hp_ne_two hζ e hy :
          FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_mul,
      a_eta_zero_dvd_p_pow_spec hp_ne_two hζ e hy]
  -- `𝔞(η)/𝔞₀ = (𝔞(η)/𝔞(η₀)) · 𝔭^m`.
  have key :
      (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η :
          FractionalIdeal (𝓞 K)⁰ K) /
        (aEtaZeroDvdPPow hp_ne_two hζ e hy :
          FractionalIdeal (𝓞 K)⁰ K) =
      ((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η :
          FractionalIdeal (𝓞 K)⁰ K) /
        (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₀ :
          FractionalIdeal (𝓞 K)⁰ K)) *
        (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) ^ m := by
    rw [hcoe, div_mul_eq_mul_div,
      mul_comm (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η :
        FractionalIdeal (𝓞 K)⁰ K),
      mul_div_mul_left _ _ (pow_ne_zero m hP_ne)]
  rw [key, mul_pow]
  -- First factor principal.
  have h1 := caseII_specificQuotient_pow_isPrincipal p K hp_ne_two hζ e hy η η₀
  rw [FractionalIdeal.isPrincipal_iff] at h1
  obtain ⟨g, hg⟩ := h1
  -- Second factor is `span((ζ-1)^{mp})`, principal.
  rw [FractionalIdeal.isPrincipal_iff]
  refine ⟨g * (algebraMap (𝓞 K) K (hζ.toInteger - 1)) ^ (m * p), ?_⟩
  rw [hg, ← pow_mul, ← FractionalIdeal.coeIdeal_pow, Ideal.span_singleton_pow,
    FractionalIdeal.coeIdeal_span_singleton, map_pow,
    FractionalIdeal.spanSingleton_mul_spanSingleton]

/-- **Bridge: a real-ideal model yields the Washington fixed integral generator.**

Given a nonzero real ideal `J : Ideal (𝓞 K⁺)` whose extension equals the anchored
quotient `𝔞(η) / 𝔞₀` (for an adjacent root `η ≠ η₀`), the proven plus-class
principalization under Vandiver `¬ 37 ∣ h⁺` makes `J` itself principal in `𝓞 K⁺`,
so `a := algebraMap b` is a conjugation-fixed integral generator with `ζ - 1 ∤ a`
and the required span identity.

This discharges the entire `CaseIIWashingtonFixedIntegralGenerator37` data
**except** the real descent `𝔞(η)/𝔞₀ = J.map`, the irreducible Washington 9.4
real-expression input. -/
theorem caseII_fixedRealGenerator_of_realIdealModel
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y) (hz : ¬ hζ.toInteger - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp_ne_two hζ e hy)
    {J : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      ((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η :
          FractionalIdeal (𝓞 K)⁰ K) /
        (aEtaZeroDvdPPow hp_ne_two hζ e hy :
          FractionalIdeal (𝓞 K)⁰ K)) =
        (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ b : 𝓞 (NumberField.maximalRealSubfield K),
      ¬ (hζ.toInteger - 1) ∣
        algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b ∧
      ((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η :
          FractionalIdeal (𝓞 K)⁰ K) /
        (aEtaZeroDvdPPow hp_ne_two hζ e hy :
          FractionalIdeal (𝓞 K)⁰ K)) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b)) := by
  -- `(𝔞(η)/𝔞₀)^p` is principal (helper); transport to `(J.map)^p` via the model.
  have hJmap_pow_ideal :
      ((J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))) ^ p :
        Ideal (𝓞 K)).IsPrincipal := by
    have hsub :
        ((((J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))) ^ p :
            Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K).IsPrincipal := by
      rw [FractionalIdeal.coeIdeal_pow, ← hJ_model]
      exact caseII_a0_quotient_pow_isPrincipal hp_ne_two hζ e hy η
    exact (IsFractionRing.coeSubmodule_isPrincipal (R := 𝓞 K) (K := K)
      (I := (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))) ^ p)).mp
      (by simpa using hsub)
  -- Vandiver engine + Diekmann Prop 55 descent: `J` is principal in `𝓞 K⁺`.
  have hJmap_principal :
      (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).IsPrincipal :=
    map_isPrincipal_of_pow_principal_of_not_dvd_hPlus hp_ne_two h_not_dvd hJ_ne
      hJmap_pow_ideal
  have hJ_principal : J.IsPrincipal :=
    isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_ne_two) (K := K)
      J hJmap_principal
  obtain ⟨a₀, ha₀⟩ := hJ_principal
  -- Span identity for the extended principal ideal.
  have hJspan :
      (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) a₀)) := by
    rw [ha₀, Ideal.map_span, Set.image_singleton,
      FractionalIdeal.coeIdeal_span_singleton]
  -- `𝔞₀ ≠ 0` (else `𝔭 ∣ 𝔞₀`).
  have h_a0_ne : (aEtaZeroDvdPPow hp_ne_two hζ e hy :
      FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    intro h0
    exact not_p_div_a_zero hp_ne_two hζ e hy hz (h0 ▸ dvd_zero _)
  refine ⟨a₀, ?_, by rw [hJ_model]; exact hJspan⟩
  -- `ζ - 1 ∤ a`, from `𝔭 ∤ 𝔞(η)` (`η ≠ η₀`) and the factorisation `𝔞(η) = (a)·𝔞₀`.
  intro hdvd
  have hfac : (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η :
        FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) a₀)) *
        (aEtaZeroDvdPPow hp_ne_two hζ e hy : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hJspan, ← hJ_model, div_mul_cancel₀ _ h_a0_ne]
  have hfac_ideal :
      rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η =
        Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) a₀} :
          Set (𝓞 K)) *
          aEtaZeroDvdPPow hp_ne_two hζ e hy := by
    have hfac' := hfac
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_mul] at hfac'
    exact FractionalIdeal.coeIdeal_injective (K := K) hfac'
  have hp_a : ¬ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) ∣
      rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η := by
    rw [p_dvd_a_iff hp_ne_two hζ e hy η]
    exact hη
  apply hp_a
  rw [hfac_ideal]
  refine Dvd.dvd.mul_right ?_ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
  exact hdvd

/-- **FLT37 packaging of `caseII_fixedRealGenerator_of_realIdealModel`.** Builds the
Washington `CaseIIWashingtonFixedIntegralGenerator37` data from a real-ideal model of
the anchored quotient, at `p = 37`. -/
noncomputable def CaseIIData37.fixedIntegralGenerator_of_realIdealModel
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : η ≠ D.etaZero)
    {J : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      ((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
        (aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K)) =
        (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K)) :
    CaseIIWashingtonFixedIntegralGenerator37 D η := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have H :=
    caseII_fixedRealGenerator_of_realIdealModel (p := 37) (K := K)
      (by decide : (37 : ℕ) ≠ 2) h_not_dvd D.hζ D.equation D.hy D.hz η hη hJ_ne
      (by simpa only [CaseIIData37.rootIdeal] using hJ_model)
  exact
    { a := algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) H.choose
      fixed_eq := ringOfIntegersComplexConj_algebraMap_eq (K := K) H.choose
      not_zetaSubOne_dvd := H.choose_spec.1
      span_eq := by simpa only [CaseIIData37.rootIdeal] using H.choose_spec.2.symm }

/-- **The Case-II II1 real-ideal descent source for FLT37.** For each Case-II datum `D`
and adjacent root `η ∈ {η₀ζ, η₀ζ²}`, a nonzero ideal `J` of `𝓞 K⁺` whose extension to
`𝓞 K` is the anchored quotient `𝔞(η)/𝔞₀`. This is the irreducible Washington 9.4
real-expression input that remains for Case-II II1 (everything else is discharged by the
proven `¬ 37 ∣ h⁺`). It is strictly more concrete than the full
`WashingtonCaseIIAdjacentFixedGenerators37Source` it feeds. -/
def CaseIIRealIdealDescent37 [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Type :=
  ∀ {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
    η ≠ D.etaZero →
    { J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))) //
        J ≠ ⊥ ∧
        ((D.rootIdeal η :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ)) /
            (aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ))) =
          (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
            FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ)) }

/-- **The Washington 9.4 adjacent fixed-generator source from the real-ideal descent.**

Given the real-ideal descent of each anchored quotient `𝔞(η)/𝔞₀` (η ∈ {η₀ζ, η₀ζ²}),
the proven `¬ 37 ∣ h⁺` discharges the full
`WashingtonCaseIIAdjacentFixedGenerators37Source`.

This isolates the entire remaining Case-II II1 obligation into the real-ideal descent
`models`: that the two anchored quotients descend from ideals of the maximal real
subfield. -/
noncomputable def washingtonCaseIIAdjacentFixedGenerators37Source_of_realIdealDescent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (models : CaseIIRealIdealDescent37) :
    WashingtonCaseIIAdjacentFixedGenerators37Source :=
  fun _hV _hSO {_m} D ↦
    { atEtaOne :=
        D.fixedIntegralGenerator_of_realIdealModel h_not_dvd D.etaOne D.etaOne_ne_etaZero
          (J := (models D D.etaOne D.etaOne_ne_etaZero).1)
          (models D D.etaOne D.etaOne_ne_etaZero).2.1
          (models D D.etaOne D.etaOne_ne_etaZero).2.2
      atEtaTwo :=
        D.fixedIntegralGenerator_of_realIdealModel h_not_dvd D.etaTwo D.etaTwo_ne_etaZero
          (J := (models D D.etaTwo D.etaTwo_ne_etaZero).1)
          (models D D.etaTwo D.etaTwo_ne_etaZero).2.1
          (models D D.etaTwo D.etaTwo_ne_etaZero).2.2 }

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

end

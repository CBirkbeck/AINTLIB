import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.DescentQuotientRationalCongruence
import BernoulliRegular.FLT37.Eichler.CaseII.Section91.MembershipFreeDescentReduction

/-!
# Regular-Index Eigenspace Collapse for `p = 37`

This file packages the Washington Lemma 9.9 input used in the Case-II descent for
Fermat's Last Theorem at `p = 37`.

## Main definitions

* `DescentUnitOmega32Membership37`: the named `ω³²`-membership proposition for
  real descent units congruent to integers modulo `37`.

## Main results

* `caseIIOmega32_eigenCollapseData_of_membership`: the membership-free
  Corollary-8.15 descent data follows from `DescentUnitOmega32Membership37`.
* `caseIIOmega32_assumptionII_of_membership_localPower`: Assumption II follows
  from `DescentUnitOmega32Membership37` and `Lemma98LocalPower37`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2
  Lemma 9.9, Exercises 8.10/8.11, Corollary 8.15, and Theorem 8.16.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-- Washington Lemma 9.9 regular-index collapse for `p = 37`: a real unit whose
image in `𝓞 K` is congruent to an integer modulo `37` has mod-`37` free-part
class in the `ω³²` eigenspace. -/
def DescentUnitOmega32Membership37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
    (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) →
    FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)

open FLT37.LehmerVandiver.CaseII in
/-- The membership-free Corollary-8.15 descent data follows from the named
`ω³²`-membership input. -/
theorem caseIIOmega32_eigenCollapseData_of_membership
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hMem : DescentUnitOmega32Membership37) :
    Cor815EigenCollapseDescentData37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨u, hu⟩ := caseIISigmaAntiDescent_quotient_unitsMap D.hζ D.one_le_m hx hy hz heq
  obtain ⟨c, hc⟩ := caseII_quotient_sub_intCast_mem_37 D.hζ D.one_le_m hx heq
  refine ⟨u, ?_, hu⟩
  apply caseIIExplicitDescent_eigenCollapse_of_mem_omega32_eigenspace u
  apply hMem u c
  rw [hu]
  exact hc

open FLT37.LehmerVandiver.CaseII in
/-- Assumption II follows from `DescentUnitOmega32Membership37` and
`Lemma98LocalPower37`. -/
theorem caseIIOmega32_assumptionII_of_membership_localPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hMem : DescentUnitOmega32Membership37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIExplicitDescent_assumptionII_of_eigenCollapseData
    (caseIIOmega32_eigenCollapseData_of_membership hMem) h_localPow

end BernoulliRegular.FLT37.Eichler

end

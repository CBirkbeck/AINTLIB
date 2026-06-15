import BernoulliRegular.BernoulliFast.KellnerSecondOrder
import BernoulliRegular.FLT37.Final
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiRadicalNotPthPower
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.RealPthRootDescent
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificChain
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundleViaKellner
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.FinalSynthesis
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.CertificateAudit
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.ReflectionOther
import BernoulliRegular.HMinus.HMinusCriterion
import BernoulliRegular.Reflection.ClassGroupModP.AtomC
import BernoulliRegular.Reflection.ClassGroupModP.SP2
import BernoulliRegular.Reflection.FinalReflection.Part2
import BernoulliRegular.UnitQuotient.PadicEigenspaceRankOne

/-!
# Unconditional FLT37 with temporary source boundaries

This file ships the current final FLT37 chain with explicit temporary source
constants for the five non-Bernoulli mathematical inputs, then composes them
with the exact second-order Bernoulli target for `B_1184` to derive
`FermatLastTheoremFor 37`.  After the source-boundary refactor, the final path
has no non-Bernoulli compiled `sorry`; it is not axiom-clean until the five
temporary source constants below are replaced by Lean proofs.

## Open contracts

### Plus-class route
The broad Cor 8.19/Pollaczek endpoint is now routed through two smaller source
constants:

* `KuceraThaineComponent32Source`: the single-character Kučera/Thaine
  implication from the concrete rank-one Padic Pollaczek quotient torsion
  statement to triviality of the `ω^32` plus-class component.  The
  `ThaineSingleCharDischarge` packaging is checked below.
* `HerbrandRibetReflectedOddDataSource`: after the checked weak reflection
  step, this supplies the exact odd eigenspace data consumed by the
  Herbrand/Ribet theorem.

### `flt37_caseI_AK5a_placeholder`
Case I: prove the anti-Kummer extension attached to each actual Case-I FLT37
datum is unramified.  The checked adapter
`AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus`
then derives the reviewer-preferred `AK5a_PrincipalMinusIdeals` surface using
the already-derived plus-class non-divisibility.

### `caseII_descent_step_under_vandiver37`
Washington 9.4 Case II descent for p = 37, stated as a strict descent step on
`CaseIIData37` under `37 ∤ hPlus(K_37)` and
`NoSecondOrderIrregularPair 37 32`. The concrete real-ideal construction and
adapted Kummer unit step belong inside this descent theorem, not as separate
final endpoints.

The checked consumers immediately below this boundary reduce the missing Case-II
work to Washington's two adjacent expressions
`(ρ_a - ζρ_-a) / (1 - ζ)`, their anchored quotient span identities, and the
exact quotient-unit `37`th-power statement produced by the descent equation.

## Standalone shipped fact

* `dvd_hMinus_thirtyseven_unconditional` — `37 ∣ hMinus(K_37)`,
  axiom-clean, via Diekmann Theorem 42 + the shipped fact `37 ∣ B_32`.
  Independent of the chain composition; the "minus side" of the
  class-number factorisation already detects 37 unconditionally for the
  irregular prime 37.

## End-to-end conclusion

Combining the five temporary source constants with the target second-order
Bernoulli computation:

  `fermatLastTheoremFor_thirtyseven_unconditional : FermatLastTheoremFor 37`

Modulo: the `B_1184` second-order Bernoulli computation plus the
Kučera/Thaine, Herbrand/Ribet, Case-I AK5a, and Washington Case-II source
constants above.
-/

@[expose] public section

noncomputable section

open NumberField Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular

open FLT37.LehmerVandiver.CaseII
open FLT37.LehmerVandiver

private instance : Fact (Nat.Prime 37) := ⟨by decide⟩

private instance : NeZero (37 : ℕ) := ⟨by decide⟩

/-- **`37 ∣ hMinus(K_37)` unconditional, axiom-clean** — the minus-side
class number is divisible by 37 for the cyclotomic field `K = ℚ(ζ_37)`,
via Diekmann Theorem 42 (`p_dvd_hMinus_iff_p_dvd_some_bernoulli`) and
the irregular index witness `37 ∣ B_32` (`thirtyseven_dvd_bernoulli_thirtytwo_num`).
The witness is `k = 16` so `2k = 32` and `2k ≤ p − 3 = 34`. -/
theorem dvd_hMinus_thirtyseven_unconditional :
    (37 : ℕ) ∣ hMinus (CyclotomicField 37 ℚ) := by
  rw [p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := 37)
        (K := CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2)]
  exact ⟨16, by norm_num, by norm_num,
    by simpa using thirtyseven_dvd_bernoulli_thirtytwo_num⟩

/-- **Cor 8.19 bridge from the exact FLT37 Pollaczek root source.**

This is the public version of the private composition used by the final
placeholder chain below.  It does not prove the Pollaczek source: it only
checks that the exact canonical K⁺-side p-th-root statement is sufficient to
produce the `Cor8_19Bridge` consumed downstream. -/
theorem cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37)) :
    Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 := by
  have h_forward :
      FLT37.Sinnott.PollaczekForward 37 (CyclotomicField 37 ℚ) 32
        (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) :=
    FLT37.LehmerVandiver.CaseI.pollaczekForward_of_pollaczekUnitPlusKplus_isPthPower
      32 (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) h_pollaczek
  exact
    FLT37.Sinnott.cor8_19Bridge_closed 37 (CyclotomicField 37 ℚ) 32
      (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) h_forward

/-- **Direct Vandiver discharge from the exact FLT37 Pollaczek root source.**

The concrete local certificate proves the canonical K⁺ Pollaczek preimage is
not a 37-th power. Therefore any theorem proving that `37 ∣ h⁺` forces that
same preimage to be a 37-th power immediately gives `37 ∤ h⁺`. -/
theorem not_dvd_hPlus_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37)) :
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) := fun h_dvd ↦
  FLT37.flt37_pollaczekUnitPlusKplus_not_exists_pthPower (h_pollaczek h_dvd)

/-- **FLT37 from Cor 8.19, Stage 2, and Washington 9.4 Case-II descent.**

This is the composition-only layer separating the case-I Stage 2 source from
the case-II descent source. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_stage2 cor8_19 stage2 noSecondOrderIrregular
    (FLT37.LehmerVandiver.CaseII.caseIIBridge_thirtyseven_of_descent_step caseII_step)

/-- **FLT37 from `37 ∤ h⁺`, Stage 2, and Washington 9.4 Case-II descent.**

This direct assembly is used when the plus-class non-divisibility has already
been obtained, for example by the concrete Pollaczek contradiction above. -/
theorem fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus_stage2_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus h_not_dvd
    (FLT37.LehmerVandiver.CaseI.caseIClassEqDischarge_of_stage2 stage2)
    noSecondOrderIrregular
    (FLT37.LehmerVandiver.CaseII.caseIIBridge_thirtyseven_of_descent_step caseII_step)

private theorem stage2KummerRatioK_of_AK5a_aux
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ)) :
    FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
  FLT37.LehmerVandiver.CaseI.stage2KummerRatioK_of_AK5a (K := CyclotomicField 37 ℚ)
    (by decide : 2 < 37) (by decide : (37 : ℕ) ≠ 2) caseI_AK5a

/-- **Vandiver/second-order split for the current FLT37 proof.**

This is the conditional theorem requested by the top-level split: once
Vandiver's plus-side coprimality, the reviewer-preferred Case-I AK5a theorem,
the Washington 9.4 strict Case-II descent step, and the explicit second-order
non-irregularity input are supplied, the existing checked Lehmer--Vandiver
pipeline proves `FermatLastTheoremFor 37`.

No Pollaczek or `B_1184` computation is hidden in this statement: those are
separate producers of `Vandiver37PlusCoprime` and
`NoSecondOrderIrregularPair 37 32`. -/
theorem fermatLastTheoremFor_thirtyseven_of_vandiver37_AK5a_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_vandiver : FLT37.Vandiver37PlusCoprime)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime h_vandiver
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  exact
    fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus_stage2_caseIIDescent_noSecondOrder
      h_not_dvd stage2 caseII_step noSecondOrderIrregular

/-- **FLT37 from the exact Pollaczek root source, Stage 2, and Washington
9.4 Case-II descent.**

This version bypasses the generic `Cor8_19Bridge` adapter in the final path:
the Pollaczek root source contradicts the concrete K⁺ non-pth-power theorem
directly, giving the Vandiver input required by both cases. -/
theorem fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_stage2_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus_stage2_caseIIDescent_noSecondOrder
    (not_dvd_hPlus_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek)
    stage2 caseII_step noSecondOrderIrregular

/-- **FLT37 from Cor 8.19, AK5a, and Washington 9.4 Case-II descent.**

This is the source-faithful public composition for the current final path:
Case II is supplied as a strict descent theorem on concrete `CaseIIData37`,
rather than as separate real-ideal-model and adapted-Kummer endpoints. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseIIDescent_noSecondOrder
      cor8_19 stage2 caseII_step noSecondOrderIrregular

/-- **FLT37 from boundary-inclusive Thaine/Herbrand, AK5a, and Case-II descent.**

This is the reviewer-aligned final split with the plus-class input decomposed
into the single-character Thaine discharge at `ω^32` and a boundary-inclusive
Herbrand/Ribet bridge for the remaining reflection components. -/
theorem fermatLastTheoremFor_thirtyseven_of_thaineHerbrandAll_AK5a_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j →
        componentId.componentNontrivial j → (37 : ℤ) ∣ (_root_.bernoulli j).num)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_thirtyseven_of_thaineAndHerbrandRibet_allEven
      componentId thaine h_herbrand
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_caseIIDescent_noSecondOrder
      cor8_19 caseI_AK5a caseII_step noSecondOrderIrregular

/-- **FLT37 from the concrete Padic Pollaczek quotient, Herbrand, AK5a, and
Case-II descent.**

The Pollaczek rank-one quotient torsion statement is already proved
unconditionally in `PadicEigenspaceRankOne`.  This endpoint leaves only the
Kučera/Thaine class-group implication from that concrete quotient to
`¬ componentNontrivial 32` as the plus-class source input. -/
theorem fermatLastTheoremFor_thirtyseven_of_padicThaineHerbrandAll_AK5a_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (h_thaine :
      (∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
          Submodule.span ℤ_[37]
            ({(FLT37.flt37_pollaczekUnit_padic_eigenspace_class :
                cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                  (CyclotomicField 37 ℚ)
                  (cyclotomicOmegaPadicChar (p := 37) 32))} : Set _),
        ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0) →
      ¬ componentId.componentNontrivial 32)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j →
        componentId.componentNontrivial j → (37 : ℤ) ∣ (_root_.bernoulli j).num)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32 :=
    FLT37.thaineSingleCharDischarge37_of_padicEigenspaceQuotient
      componentId h_thaine
  exact
    fermatLastTheoremFor_thirtyseven_of_thaineHerbrandAll_AK5a_caseIIDescent_noSecondOrder
      componentId thaine h_herbrand caseI_AK5a caseII_step
      noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from the concrete Padic Thaine input, named Case-I AK
unramifiedness, and adjacent Case-II generator/unit-power data.**

This is the currently sharpest proof-clean assembly theorem for the
non-Bernoulli part: the plus-class route is exposed at the concrete Padic
quotient-to-class-group implication, Case I is exposed at the named
anti-Kummer unramified source, and Case II is exposed at the two anchored
quotient generators plus the exact quotient-unit p-th-power source. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_padicThaineHerbrand_CaseIAntiKummer_adjacentCaseIIGeneratorsUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (h_thaine :
      (∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
          Submodule.span ℤ_[37]
            ({(FLT37.flt37_pollaczekUnit_padic_eigenspace_class :
                cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                  (CyclotomicField 37 ℚ)
                  (cyclotomicOmegaPadicChar (p := 37) 32))} : Set _),
        ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0) →
      ¬ componentId.componentNontrivial 32)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j →
        componentId.componentNontrivial j → (37 : ℤ) ∣ (_root_.bernoulli j).num)
    (h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ b₁ a₂ b₂ : 𝓞 (CyclotomicField 37 ℚ),
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₁ / b₁ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₂ / b₂ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32 :=
    FLT37.thaineSingleCharDischarge37_of_padicEigenspaceQuotient
      componentId h_thaine
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_thirtyseven_of_thaineAndHerbrandRibet_allEven
      componentId thaine h_herbrand
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19
      cor8_19
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
      h_not_dvd h_LK
  exact
    fermatLastTheoremFor_thirtyseven_of_padicThaineHerbrandAll_AK5a_caseIIDescent_noSecondOrder
      componentId h_thaine h_herbrand caseI_AK5a
      (fun hV hSO {_m} D ↦
        FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
          (fun {_m'} D' ↦ hgens hV hSO D')
          (fun {_m'} D' ↦ h_unit hV hSO D') D)
      noSecondOrderIrregular

set_option maxRecDepth 40000 in
/-- **FLT37 from Cor 8.19, the concrete Case-I factor-class target, and
Washington 9.4 Case-II descent.**

This is the direct descent-boundary version of the stronger Case-I route:
once every actual Case-I factor ideal class is trivial, the existing Stage 2
reduction supplies the Case-I input without passing through AK-5a as an
extra public source. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_factorIdealClass_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_factor_class :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37) →
        ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
            nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) = 1)
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.stage2KummerRatioK_of_factorIdeal_class_eq_one
      (K := CyclotomicField 37 ℚ) (by decide : 2 < 37)
      (by decide : (37 : ℕ) ≠ 2) caseI_factor_class
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseIIDescent_noSecondOrder
      cor8_19 stage2 caseII_step noSecondOrderIrregular

set_option linter.style.longLine false in
set_option maxRecDepth 40000 in
/-- **FLT37 from the exact Pollaczek root source, principality of the actual
Case-I factor ideals, and Washington 9.4 Case-II descent.**

This is a stronger Case-I route than the final private AK5a source.
It is useful when the AK-chain produces a principal generator for the
actual factor ideal directly. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_factorIdealPrincipal_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_principal :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, I ≠ ⊥ →
        Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37 →
        I.IsPrincipal)
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.stage2KummerRatioK_of_factorIdeal_isPrincipal
      (K := CyclotomicField 37 ℚ) (by decide : 2 < 37)
      (by decide : (37 : ℕ) ≠ 2) caseI_principal
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseIIDescent_noSecondOrder
      cor8_19 stage2 caseII_step noSecondOrderIrregular

set_option maxRecDepth 40000 in
/-- **FLT37 from Cor 8.19, the concrete Case-I square-class target, and
Washington 9.4 Case-II descent.**

This is a checked intermediate route for the AK-1..AK-4 work: once the actual
case-I factor ideals satisfy `[σI]^2 = [I]^2`, the existing p-torsion,
class-equality, AK-5a, and Stage 2 infrastructure supply the Case-I input.
The final theorem is not rewired to this as a new placeholder. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_caseISquare_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_square :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
          Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
            ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
              Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37 →
          (ClassGroup.mk0
              (⟨I.map
                (NumberField.IsCMField.ringOfIntegersComplexConj
                  (CyclotomicField 37 ℚ)).toRingEquiv.toRingHom,
                mem_nonZeroDivisors_iff_ne_zero.mpr
                  ((FLT37.map_ne_bot_iff_complexConj
                    (CyclotomicField 37 ℚ) I).mpr hI_ne)⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) ^ 2) =
            (ClassGroup.mk0
              (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) ^ 2))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    CaseI.stage2KummerRatioK_of_factor_class_square_eq_and_not_dvd_hPlus_cyclotomic
      (by decide : 2 < 37)
      (by decide : (37 : ℕ) ≠ 2) h_not_dvd caseI_square
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseIIDescent_noSecondOrder
      cor8_19 stage2 caseII_step noSecondOrderIrregular

set_option maxRecDepth 40000 in
/-- **FLT37 from Cor 8.19, the direct AK-5 unit-form/congruence target, and
Washington 9.4 Case-II descent.**

This checked route bypasses the broad AK-5a endpoint when the source work
already produces the exact unit form needed by AK-5b and the `u ≡ 1 mod 37`
input needed by AK-5c. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_caseIAK5UnitCongr_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5 :
      ∀ {a b c : ℤ}
        (_heq : a ^ 37 + b ^ 37 = c ^ 37)
        (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
        {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
        (hab : ¬ (a = 0 ∧ b = 0))
        (I : Ideal (𝓞 (CyclotomicField 37 ℚ))) (_hI_ne : I ≠ ⊥)
        (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37),
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (u : 𝓞 (CyclotomicField 37 ℚ)) * γ ^ 37 =
            FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              (CyclotomicField 37 ℚ) a b ζ hab ∧
          (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
            (↑u : 𝓞 (CyclotomicField 37 ℚ)) - 1)
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    CaseI.stage2KummerRatioK_of_AK5_unit_form_and_p_congr_cyclotomic
      (p := 37) (by decide : (37 : ℕ) ≠ 2)
      (by decide : (37 : ℕ) ≠ 3) h_not_dvd caseI_AK5
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseIIDescent_noSecondOrder
      cor8_19 stage2 caseII_step noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from the exact Pollaczek root source, the direct AK-5
unit-form/congruence target, and Washington 9.4 Case-II descent.** -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseIAK5UnitCongr_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_AK5 :
      ∀ {a b c : ℤ}
        (_heq : a ^ 37 + b ^ 37 = c ^ 37)
        (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
        {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
        (hab : ¬ (a = 0 ∧ b = 0))
        (I : Ideal (𝓞 (CyclotomicField 37 ℚ))) (_hI_ne : I ≠ ⊥)
        (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37),
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (u : 𝓞 (CyclotomicField 37 ℚ)) * γ ^ 37 =
            FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              (CyclotomicField 37 ℚ) a b ζ hab ∧
          (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
            (↑u : 𝓞 (CyclotomicField 37 ℚ)) - 1)
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_cor8_19_caseIAK5UnitCongr_caseIIDescent_noSecondOrder
    (cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek)
    caseI_AK5 caseII_step noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from the exact Pollaczek root source, direct AK-5
unit-form/congruence, adjacent Washington generators, and the exact Case-II
quotient-unit p-th-power source.**

This is the exact-Pollaczek version of the narrowed Case-II endpoint: the
Case-II input no longer exposes the broad `AdaptedKummersLemmaOnSpecific`,
only the p-th-power conclusion for the specific quotient unit appearing in
the two-generator Washington descent formula. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseIAK5UnitCongr_adjacentWashingtonUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_AK5 :
      ∀ {a b c : ℤ}
        (_heq : a ^ 37 + b ^ 37 = c ^ 37)
        (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
        {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
        (hab : ¬ (a = 0 ∧ b = 0))
        (I : Ideal (𝓞 (CyclotomicField 37 ℚ))) (_hI_ne : I ≠ ⊥)
        (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37),
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (u : 𝓞 (CyclotomicField 37 ℚ)) * γ ^ 37 =
            FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              (CyclotomicField 37 ℚ) a b ζ hab ∧
          (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
            (↑u : 𝓞 (CyclotomicField 37 ℚ)) - 1)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseIAK5UnitCongr_caseIIDescent_noSecondOrder
    h_pollaczek caseI_AK5
    (fun hV hSO {_m} D ↦
      FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_unitPower
        (fun {_m'} D' ↦ hgens hV hSO D')
        (fun {_m'} D' ↦ h_unit hV hSO D') D)
    noSecondOrderIrregular

/-- **FLT37 from the exact Pollaczek root source, AK5a, and Washington 9.4
Case-II descent.**

This expands the Cor 8.19 input to the canonical real Pollaczek-unit p-th-root
statement while keeping the Case-II input at the descent-step boundary. -/
theorem fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5a_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_caseIIDescent_noSecondOrder
    (cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek)
    caseI_AK5a caseII_step noSecondOrderIrregular

set_option maxRecDepth 40000 in
/-- **FLT37 from the exact Pollaczek root source, concrete Case-I
Hilbert-90 cross-multiplication data, and Washington 9.4 Case-II descent.**

This is the AK-1..AK-4-facing final bridge.  The Case-I input is not a generic
minus-principality theorem: it is the concrete witness `δ` for actual case-I
factor ideals satisfying `I · (σδ) = σI · (δ)`, plus the nonzero localization
side conditions needed by the existing class-group descent chain. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseICrossMul_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_cross_data :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37) →
        ∃ δ : (CyclotomicField 37 ℚ)ˣ,
          ((I : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) *
              FractionalIdeal.spanSingleton
                (𝓞 (CyclotomicField 37 ℚ))⁰
                (NumberField.IsCMField.complexConj
                  (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ)) =
            ((I.map
              (NumberField.IsCMField.ringOfIntegersComplexConj
                (CyclotomicField 37 ℚ)).toRingEquiv.toRingHom :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) *
              FractionalIdeal.spanSingleton
                (𝓞 (CyclotomicField 37 ℚ))⁰
                (δ : CyclotomicField 37 ℚ))) ∧
          ((IsLocalization.sec (𝓞 (CyclotomicField 37 ℚ))⁰
            (NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ)
              (δ : CyclotomicField 37 ℚ) * ((δ : CyclotomicField 37 ℚ))⁻¹)).1 :
              𝓞 (CyclotomicField 37 ℚ)) ≠ 0 ∧
          ((IsLocalization.sec (𝓞 (CyclotomicField 37 ℚ))⁰
            (NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ)
              (δ : CyclotomicField 37 ℚ) * ((δ : CyclotomicField 37 ℚ))⁻¹)).2 :
              𝓞 (CyclotomicField 37 ℚ)) ≠ 0)
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals_of_cross_mul_data_and_not_dvd_hPlus
      (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide : (37 : ℕ) ≠ 2) h_not_dvd caseI_cross_data
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_caseIIDescent_noSecondOrder
      cor8_19 caseI_AK5a caseII_step noSecondOrderIrregular

set_option linter.style.longLine false in
set_option maxRecDepth 40000 in
/-- **FLT37 from the exact Pollaczek root source, concrete Case-I
Hilbert-90 cross-multiplication witnesses, and Washington 9.4 Case-II descent.**

Compared with
`fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseICrossMul_caseIIDescent_noSecondOrder`,
the nonzero localization side conditions are no longer source inputs: they are
proved automatically from `δ : Kˣ`. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseICrossMulWitness_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_cross_data :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37) →
        ∃ δ : (CyclotomicField 37 ℚ)ˣ,
          ((I : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) *
              FractionalIdeal.spanSingleton
                (𝓞 (CyclotomicField 37 ℚ))⁰
                (NumberField.IsCMField.complexConj
                  (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ)) =
            ((I.map
              (NumberField.IsCMField.ringOfIntegersComplexConj
                (CyclotomicField 37 ℚ)).toRingEquiv.toRingHom :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) *
              FractionalIdeal.spanSingleton
                (𝓞 (CyclotomicField 37 ℚ))⁰
                (δ : CyclotomicField 37 ℚ))))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) := by
    intro a b c hgcd hcaseI heq ζ hζ I hI_ne hI_pow
    exact
      (FLT37.LehmerVandiver.CaseI.stage2KummerRatioK_of_cross_mul_witness_and_not_dvd_hPlus
        (p := 37) (K := CyclotomicField 37 ℚ)
        (by decide : 2 < 37) (by decide : (37 : ℕ) ≠ 2) h_not_dvd
        caseI_cross_data)
        hgcd hcaseI heq hζ hI_ne hI_pow
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseIIDescent_noSecondOrder
      cor8_19 stage2 caseII_step noSecondOrderIrregular

/-- **FLT37 from the exact Pollaczek root source, the AK-chain
unramifiedness target for Case I, and Washington 9.4 Case-II descent.**

This is the AK-1..AK-4-facing alternative to the AK5a bridge above.  Its
Case-I input is the concrete per-case statement that the anti-Kummer lift
attached to the actual σ-anti radical is unramified over `K`; the existing
AK machinery then applies the Hilbert 94 obstruction under `37 ∤ h⁺`. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AKchain_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (_heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := 37) (CyclotomicField 37 ℚ)
          (FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab)
          (FLT37.LehmerVandiver.CaseI.caseI_antiRadical_ne_zero
            (K := CyclotomicField 37 ℚ)
            (by decide : (37 : ℕ) ≠ 2) hcaseI hζ hab))))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek
  exact
    CaseI.fermatLastTheoremFor_thirtyseven_via_AK_chain_of_cor8_19_and_noSecondOrder
      cor8_19 h_LK_unram_per_case noSecondOrderIrregular
      (caseIIBridge_thirtyseven_of_descent_step caseII_step)

/-- **FLT37 from refined Thaine, AK-chain unramifiedness, and Case-II descent.**

This endpoint uses the reviewer-preferred source surfaces without exposing
`Cor8_19Bridge` or `AK5a` as monoliths.  The refined Thaine bridge gives the
exact Pollaczek root source; the AK unramified source gives AK5a under the
resulting `37 ∤ h⁺`; the checked final assembly then consumes AK5a and the
Washington Case-II descent step. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_AKunramified_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (_heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := 37) (CyclotomicField 37 ℚ)
          (FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab)
          (FLT37.LehmerVandiver.CaseI.caseI_antiRadical_ne_zero
            (K := CyclotomicField 37 ℚ)
            (by decide : (37 : ℕ) ≠ 2) hcaseI hζ hab))))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) :=
    CaseI.flt37_pollaczekUnitPlusKplus_isPthPower_of_refinedThaineBridge thaine
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    not_dvd_hPlus_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek
  have h_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals_of_AK_unramified_and_not_dvd_hPlus
      (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide : (37 : ℕ) ≠ 2) (by decide : (37 : ℕ) ≠ 3)
      h_not_dvd h_LK_unram_per_case
  exact
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5a_caseIIDescent_noSecondOrder
      h_pollaczek h_AK5a caseII_step noSecondOrderIrregular

/-- **FLT37 from refined Thaine, named Case-I AK unramifiedness, and Case-II
descent.**

This is the same checked endpoint as
`fermatLastTheoremFor_thirtyseven_of_refinedThaine_AKunramified_caseIIDescent_noSecondOrder`,
but it consumes the named `CaseIAntiKummerLKUnramified` predicate. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAntiKummer_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_refinedThaine_AKunramified_caseIIDescent_noSecondOrder
    thaine
    (fun {_a _b _c} heq hcaseI {_ζ} hζ hab ↦
      h_LK heq hcaseI hζ hab)
    caseII_step noSecondOrderIrregular

/-- **FLT37 from the exact Pollaczek root source, the concrete Case-I
square-class target, and Washington 9.4 Case-II descent.**

This is the exact-Pollaczek version of
`fermatLastTheoremFor_thirtyseven_of_cor8_19_caseISquare_caseIIDescent_noSecondOrder`.
The case-I input remains the concrete `[σI]^2 = [I]^2` target for actual
case-I factor ideals. -/
theorem fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseISquare_caseIIDescent_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_square :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
          Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
            ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
              Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37 →
          (ClassGroup.mk0
              (⟨I.map
                (NumberField.IsCMField.ringOfIntegersComplexConj
                  (CyclotomicField 37 ℚ)).toRingEquiv.toRingHom,
                mem_nonZeroDivisors_iff_ne_zero.mpr
                  ((FLT37.map_ne_bot_iff_complexConj
                    (CyclotomicField 37 ℚ) I).mpr hI_ne)⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) ^ 2) =
            (ClassGroup.mk0
              (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) ^ 2))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_cor8_19_caseISquare_caseIIDescent_noSecondOrder
    (cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek)
    caseI_square caseII_step noSecondOrderIrregular

/-- **FLT37 from the exact Pollaczek root source, the concrete Case-I
square-class target, and Washington 9.4 Case-II descent**, using the
repository's current second-order endpoint. -/
theorem fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseISquare_caseIIDescent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_square :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
          Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
            ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
              Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37 →
          (ClassGroup.mk0
              (⟨I.map
                (NumberField.IsCMField.ringOfIntegersComplexConj
                  (CyclotomicField 37 ℚ)).toRingEquiv.toRingHom,
                mem_nonZeroDivisors_iff_ne_zero.mpr
                  ((FLT37.map_ne_bot_iff_complexConj
                    (CyclotomicField 37 ℚ) I).mpr hI_ne)⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) ^ 2) =
            (ClassGroup.mk0
              (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) ^ 2))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_caseISquare_caseIIDescent_noSecondOrder
    h_pollaczek caseI_square caseII_step
    (noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner kellner)

/-- **FLT37 from the currently narrowest source surfaces.**

This theorem composes the reductions that are now proved in Lean:

* `Cor8_19Bridge` gives `¬ 37 ∣ hPlus`.
* `AK5a_PrincipalMinusIdeals` gives the Stage 2 Kummer ratio.
* The off-diagonal real-ideal model plus the specific Kummer lemma gives the
  case-II bridge.

It intentionally keeps those source inputs explicit; it does not change the
unconditional endpoint theorem or add hypotheses to it. -/
theorem fermatLastTheoremFor_thirtyseven_of_sources_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (h_model_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_cor8_19_realIdealModel_ne_and_specificKummer
      cor8_19 h_model_ne h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19 stage2 noSecondOrderIrregular caseII

/-- **FLT37 from Cor 8.19, AK5a, integral real generators for Case II, and
the specific Kummer step.**

This is the generator-level variant of
`fermatLastTheoremFor_thirtyseven_of_sources_and_noSecondOrder`: the Case-II
source no longer exposes an intermediate real ideal, only the concrete
nonzero integral real generator of each quotient `A_η₁ / A_η₂`. -/
theorem fermatLastTheoremFor_thirtyseven_of_integralRealGenerators_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (hgen_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ b : 𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)),
        b ≠ 0 ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) =
            FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ)
                (algebraMap
                  (𝓞 (NumberField.maximalRealSubfield
                    (CyclotomicField 37 ℚ)))
                  (𝓞 (CyclotomicField 37 ℚ)) b))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime
      (FLT37.vandiver37PlusCoprime_of_bridge cor8_19
        FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete)
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_integral_real_generators_ne_and_adaptedKummer_via_descent
      h_not_dvd hgen_ne h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19 stage2 noSecondOrderIrregular caseII

/-- **FLT37 from Cor 8.19, AK5a, adjacent Case-II quotient generators, and
the specific Kummer step.**

This is the narrowest checked Case-II source surface: for each
`CaseIIData37` datum, it asks only for the two anchored generator identities
used by the descent equation, namely `A_{η₀ζ} / A_η₀` and
`A_{η₀ζ²} / A_η₀`. -/
theorem fermatLastTheoremFor_thirtyseven_of_adjacentCaseIIGenerators_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ b₁ a₂ b₂ : 𝓞 (CyclotomicField 37 ℚ),
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₁ / b₁ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₂ / b₂ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer_via_descent
      hgens h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19 stage2 noSecondOrderIrregular caseII

/-- **FLT37 from Cor 8.19, AK5a, adjacent integral real Case-II generators,
and the specific Kummer step.**

This is the current closest checked endpoint to the reviewer-requested
Washington real-expression proof: for each `CaseIIData37` datum, it only asks
for integral real generators of the two adjacent anchored quotients
`A_{η₀ζ} / A_η₀` and `A_{η₀ζ²} / A_η₀`, plus the internal adapted Kummer
step. -/
theorem fermatLastTheoremFor_thirtyseven_of_adjacentIntegralRealCaseIIGenerators_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ b₁ b₂ : 𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)),
          b₁ ≠ 0 ∧ b₂ ≠ 0 ∧
          ¬ (D.hζ.toInteger - 1) ∣
            algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ)) b₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣
            algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ)) b₂ ∧
          FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                (algebraMap
                  (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
                  (𝓞 (CyclotomicField 37 ℚ)) b₁)) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                (algebraMap
                  (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
                  (𝓞 (CyclotomicField 37 ℚ)) b₂)) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_adjacent_integral_real_generators_and_adaptedKummer_via_descent
      hgens h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19 stage2 noSecondOrderIrregular caseII

/-- **FLT37 from Cor 8.19, AK5a, adjacent fixed integral Case-II generators,
and the specific Kummer step.**

This endpoint lets the Washington real-expression work stay in `𝓞 K`: it asks
for the two adjacent quotient generators, fixed by complex conjugation, and
the checked Case-II bridge descends them to `𝓞 K⁺`. -/
theorem fermatLastTheoremFor_thirtyseven_of_adjacentFixedIntegralCaseIIGenerators_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ : 𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) a₁ = a₁ ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) a₂ = a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_adjacent_fixed_integral_generators_and_adaptedKummer_via_descent
      hgens h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19 stage2 noSecondOrderIrregular caseII

/-- **FLT37 from Cor 8.19, AK5a, adjacent Washington Case-II expressions,
and the specific Kummer step.**

This is the current Washington-facing Case-II composition: the caller supplies
the two adjacent integral expressions `(rho - ζ rho') / (1 - ζ)` and their
span identities.  The fixedness of those expressions is checked internally by
`washington_integral_expression_fixed_of_primitive_integer_conj_pair`. -/
theorem fermatLastTheoremFor_thirtyseven_of_adjacentWashingtonCaseII_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁_neg = rho₁ ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂_neg = rho₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge37_of_adjacent_washingtonExpr_and_adaptedKummer_via_descent
      hgens h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19 stage2 noSecondOrderIrregular caseII

/-- **FLT37 from refined Thaine, named AK unramifiedness, adjacent fixed
Case-II generators, and the specific adapted Kummer step.**

This is the most concrete currently wired public endpoint: it replaces the
final monolithic Pollaczek, AK5a, and Case-II descent surfaces by their
reviewer-facing source forms without adding any hypothesis to the private
`fermatLastTheoremFor_thirtyseven_unconditional` theorem. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentFixedCaseII_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ : 𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) a₁ = a₁ ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) a₂ = a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_of_refined
      (p := 37) (K := CyclotomicField 37 ℚ) thaine
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
      h_not_dvd h_LK
  exact
    fermatLastTheoremFor_thirtyseven_of_adjacentFixedIntegralCaseIIGenerators_and_noSecondOrder
      cor8_19 caseI_AK5a hgens h_kummer noSecondOrderIrregular

/-- **FLT37 from refined Thaine, named AK unramifiedness, Washington Case-II
expressions, and the specific adapted Kummer step.**

This is the reviewer-shaped version of
`fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentFixedCaseII_noSecondOrder`:
the Case-II input is no longer an abstract pair of fixed integral generators.
It supplies the two concrete Washington expressions
`(rho - ζ rho') / (1 - ζ)` together with their conjugacy and span identities;
the fixedness proof is checked inside the Case-II bridge. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentWashingtonCaseII_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁_neg = rho₁ ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂_neg = rho₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_of_refined
      (p := 37) (K := CyclotomicField 37 ℚ) thaine
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
      h_not_dvd h_LK
  exact
    fermatLastTheoremFor_thirtyseven_of_adjacentWashingtonCaseII_and_noSecondOrder
      cor8_19 caseI_AK5a hgens h_kummer noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from refined Thaine, named AK unramifiedness, and Washington
Case-II expressions with one conjugacy orientation.**

This is the narrowest currently wired source surface for the combined
non-Bernoulli path: the Case-II caller proves only `σ(rho) = rho'` for each
Washington expression.  The reverse conjugacy is derived internally from
involutivity. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentWashingtonOneConj_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentWashingtonCaseII_noSecondOrder
    thaine h_LK
    (fun hV hSO {_m} D ↦ by
      rcases hgens hV hSO D with
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg, ha₁, ha₂,
          heq₁, heq₂, hρ₁, hρ₂, hnot₁, hnot₂, hspan₁, hspan₂⟩
      refine
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg, ha₁, ha₂,
          heq₁, heq₂, hρ₁, ?_, hρ₂, ?_, hnot₁, hnot₂, hspan₁, hspan₂⟩
      · exact
          FLT37.LehmerVandiver.CaseII.ringOfIntegersComplexConj_eq_symm_of_eq
            (K := CyclotomicField 37 ℚ) hρ₁
      · exact
          FLT37.LehmerVandiver.CaseII.ringOfIntegersComplexConj_eq_symm_of_eq
            (K := CyclotomicField 37 ℚ) hρ₂)
    h_kummer noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from refined Thaine, named AK unramifiedness, and the narrowed
Washington Case-II expression source.**

This removes the redundant nonzero assumptions from
`fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentWashingtonOneConj_noSecondOrder`:
nonzero follows from the required `ζ - 1` nondivisibility of the two
Washington generators. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentWashingtonNoNonzero_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_refinedThaine_CaseIAK_adjacentWashingtonOneConj_noSecondOrder
    thaine h_LK
    (fun hV hSO {_m} D ↦ by
      rcases hgens hV hSO D with
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg,
          heq₁, heq₂, hρ₁, hρ₂, hnot₁, hnot₂, hspan₁, hspan₂⟩
      refine
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg,
          ?_, ?_, heq₁, heq₂, hρ₁, hρ₂, hnot₁, hnot₂, hspan₁, hspan₂⟩
      · exact FLT37.LehmerVandiver.CaseII.ne_zero_of_not_dvd hnot₁
      · exact FLT37.LehmerVandiver.CaseII.ne_zero_of_not_dvd hnot₂)
    h_kummer noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from exact Pollaczek, universal AK-5 data, and the narrowed
Washington Case-II expression source.**

This replaces the named `CaseIAntiKummerLKUnramified` Case-I input by the
already-checked universal AK-5 producer: for each actual case-I FLT datum, the
producer gives the anti-radical unit form and the strong `ζ' - 1`
congruence.  The existing AK chain converts that data into AK5a under the
Pollaczek-derived Vandiver input. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5Universal_adjacentWashingtonNoNonzero_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (h_AK5 : ∀ {a b c : ℤ}
      (heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0) (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified :=
    FLT37.LehmerVandiver.CaseI.caseIAntiKummerLKUnramified_of_AK5_universal
      h_AK5
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    not_dvd_hPlus_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
      h_not_dvd h_LK
  exact
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5a_caseIIDescent_noSecondOrder
      h_pollaczek caseI_AK5a
      (fun hV hSO {_m} D ↦
        FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_adaptedKummer
          (fun {_m'} D' ↦ hgens hV hSO D') (h_kummer hV hSO) D)
      noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from exact Pollaczek, universal AK-5 data, and the exact
Case-II quotient-unit p-th-power source.**

This is the unitPower refinement of
`fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5Universal_adjacentWashingtonNoNonzero_noSecondOrder`.
The Case-I source remains the universal AK-5 unit-form/strong-primarity
producer, while the Case-II source is narrowed to the specific quotient unit
appearing in Washington's two-generator descent equation. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (h_AK5 : ∀ {a b c : ℤ}
      (heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
        (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  have h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified :=
    FLT37.LehmerVandiver.CaseI.caseIAntiKummerLKUnramified_of_AK5_universal
      h_AK5
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    not_dvd_hPlus_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
      h_not_dvd h_LK
  exact
    fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5a_caseIIDescent_noSecondOrder
      h_pollaczek caseI_AK5a
      (fun hV hSO {_m} D ↦
        FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_unitPower
          (fun {_m'} D' ↦ hgens hV hSO D')
          (fun {_m'} D' ↦ h_unit hV hSO D') D)
      noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from refined Thaine, universal AK-5 data, and the narrowed
Washington Case-II expression source.**

This is the refined-Thaine variant of
`fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5Universal_adjacentWashingtonNoNonzero_noSecondOrder`.
It keeps the remaining Case-I and Case-II source work at the concrete AK-5 and
Washington-expression surfaces. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_AK5Universal_adjacentWashingtonNoNonzero_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_AK5 : ∀ {a b c : ℤ}
      (heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0) (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5Universal_adjacentWashingtonNoNonzero_noSecondOrder
    (CaseI.flt37_pollaczekUnitPlusKplus_isPthPower_of_refinedThaineBridge thaine)
    h_AK5 hgens h_kummer noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from refined Thaine, universal AK-5 data, and the exact Case-II
quotient-unit p-th-power source.**

This is the refined-Thaine version of
`fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder`.
It keeps the Case-II adapted-unit input at the exact quotient unit produced by
Washington's two-generator descent formula. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (thaine : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32)
    (h_AK5 : ∀ {a b c : ℤ}
      (heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
        (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder
    (CaseI.flt37_pollaczekUnitPlusKplus_isPthPower_of_refinedThaineBridge thaine)
    h_AK5 hgens h_unit noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from explicit Thaine/reflection fields, universal AK-5 data, and
the narrowed Washington Case-II expression source.**

This avoids bundling the Pollaczek route as `FLT37UnitClassBridgeRefined`:
the inputs are the eigenspace identification, the single-character Thaine
discharge, and the reflection discharge for the other components. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_thaineAndReflection_AK5Universal_adjacentWashingtonNoNonzero_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (h_AK5 : ∀ {a b c : ℤ}
      (heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0) (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_of_thaineAndReflection
      (p := 37) (K := CyclotomicField 37 ℚ)
      componentId thaine reflection
  have h_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified :=
    FLT37.LehmerVandiver.CaseI.caseIAntiKummerLKUnramified_of_AK5_universal
      h_AK5
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.not_dvd_hPlus_thirtyseven_of_cor8_19
      cor8_19
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
      h_not_dvd h_LK
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_caseIIDescent_noSecondOrder
      cor8_19 caseI_AK5a
      (fun hV hSO {_m} D ↦
        FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_adaptedKummer
          (fun {_m'} D' ↦ hgens hV hSO D') (h_kummer hV hSO) D)
      noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from explicit Thaine/reflection fields, universal AK-5 data, and
the exact Case-II quotient-unit p-th-power source.**

This is the explicit-component version of
`fermatLastTheoremFor_thirtyseven_of_refinedThaine_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder`;
it avoids the bundled refined bridge while still keeping Case II at the exact
quotient-unit source surface. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_thaineAndReflection_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (h_AK5 : ∀ {a b c : ℤ}
      (heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
        (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let refined : FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32 :=
    { identification := componentId
      pollaczekUnitComponent := thaine.thaine_at_i
      reflectionOtherComponents := reflection.reflection_other }
  exact
    fermatLastTheoremFor_thirtyseven_of_refinedThaine_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder
      refined h_AK5 hgens h_unit noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from Thaine, Herbrand-Ribet reflection data, universal AK-5 data,
and the exact Case-II quotient-unit p-th-power source.**

This is the Herbrand-reflection split of
`fermatLastTheoremFor_thirtyseven_of_thaineAndReflection_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder`.
The reflection side is given by the boundary component at `36` plus the
Herbrand-range implication; the existing `UniqueIrregularIndex 37 32`
certificate excludes all other even reflection components. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_thaineHR_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (h_boundary : ¬ componentId.componentNontrivial 36)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
        componentId.componentNontrivial j → (37 : ℤ) ∣ (_root_.bernoulli j).num)
    (h_AK5 : ∀ {a b c : ℤ}
      (heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0))
      {ζ' : CyclotomicField 37 ℚ} (hζ' : IsPrimitiveRoot ζ' 37),
      ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
        (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
            (γ ^ 37) =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab ∧
        (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((↑u : 𝓞 _) - 1))
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) componentId 32 :=
    reflectionOtherDischarge_thirtyseven_of_boundary_and_herbrandRibet
      componentId h_boundary h_herbrand
  exact
    fermatLastTheoremFor_thirtyseven_of_thaineAndReflection_AK5Universal_adjacentWashingtonUnitPower_noSecondOrder
      componentId thaine reflection h_AK5 hgens h_unit noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from explicit Thaine/reflection fields, direct AK-5
unit-form/congruence data, and the narrowed Washington Case-II source.**

This is the smallest currently wired Case-I surface for this Thaine route: for
each actual factor ideal it asks directly for `α₀ = u * γ^37` and
`37 ∣ u - 1`, then uses the existing AK-5c lift and Hilbert-94 contradiction
to obtain Stage 2. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_thaineAndReflection_caseIAK5UnitCongr_adjacentWashingtonNoNonzero_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (caseI_AK5 :
      ∀ {a b c : ℤ}
        (_heq : a ^ 37 + b ^ 37 = c ^ 37)
        (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
        {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
        (hab : ¬ (a = 0 ∧ b = 0))
        (I : Ideal (𝓞 (CyclotomicField 37 ℚ))) (_hI_ne : I ≠ ⊥)
        (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37),
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (u : 𝓞 (CyclotomicField 37 ℚ)) * γ ^ 37 =
            FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              (CyclotomicField 37 ℚ) a b ζ hab ∧
          (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
            (↑u : 𝓞 (CyclotomicField 37 ℚ)) - 1)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_of_thaineAndReflection
      (p := 37) (K := CyclotomicField 37 ℚ)
      componentId thaine reflection
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_caseIAK5UnitCongr_caseIIDescent_noSecondOrder
      cor8_19 caseI_AK5
      (fun hV hSO {_m} D ↦
        FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_adaptedKummer
          (fun {_m'} D' ↦ hgens hV hSO D') (h_kummer hV hSO) D)
      noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from Thaine, Herbrand-Ribet reflection data, direct AK-5
unit congruence, and the narrowed Washington Case-II source.**

This is the same final route as
`fermatLastTheoremFor_thirtyseven_of_thaineAndReflection_caseIAK5UnitCongr_adjacentWashingtonNoNonzero_noSecondOrder`,
but it no longer takes `ReflectionOtherDischarge` as a bundled source input.
The reflection side is split into the explicit boundary component at `36` and
the Herbrand-range implication from component non-triviality to Bernoulli
divisibility.  The exclusion of all even indices other than `32` is proved
from the existing `UniqueIrregularIndex.thirtyseven_thirtytwo` certificate. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_thaineHR_caseIAK5UnitCongr_adjacentWashingtonNoNonzero_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (h_boundary : ¬ componentId.componentNontrivial 36)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
        componentId.componentNontrivial j → (37 : ℤ) ∣ (_root_.bernoulli j).num)
    (caseI_AK5 :
      ∀ {a b c : ℤ}
        (_heq : a ^ 37 + b ^ 37 = c ^ 37)
        (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
        {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
        (hab : ¬ (a = 0 ∧ b = 0))
        (I : Ideal (𝓞 (CyclotomicField 37 ℚ))) (_hI_ne : I ≠ ⊥)
        (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37),
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (u : 𝓞 (CyclotomicField 37 ℚ)) * γ ^ 37 =
            FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              (CyclotomicField 37 ℚ) a b ζ hab ∧
          (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
            (↑u : 𝓞 (CyclotomicField 37 ℚ)) - 1)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) componentId 32 :=
    reflectionOtherDischarge_thirtyseven_of_boundary_and_herbrandRibet
      componentId h_boundary h_herbrand
  exact
    fermatLastTheoremFor_thirtyseven_of_thaineAndReflection_caseIAK5UnitCongr_adjacentWashingtonNoNonzero_noSecondOrder
      componentId thaine reflection caseI_AK5 hgens h_kummer
      noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from Thaine, Herbrand-Ribet reflection data, direct AK-5
unit congruence, Washington adjacent generators, and the exact Case-II
quotient-unit p-th-power source.**

This refines
`fermatLastTheoremFor_thirtyseven_of_thaineHR_caseIAK5UnitCongr_adjacentWashingtonNoNonzero_noSecondOrder`
by replacing the broad `AdaptedKummersLemmaOnSpecific` input with the exact
unit-power assertion for the quotient unit `ε₁ / ε₂` produced by the
two-generator Case-II descent formula. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_thaineHR_caseIAK5UnitCongr_adjacentWashingtonUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (h_boundary : ¬ componentId.componentNontrivial 36)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
        componentId.componentNontrivial j → (37 : ℤ) ∣ (_root_.bernoulli j).num)
    (caseI_AK5 :
      ∀ {a b c : ℤ}
        (_heq : a ^ 37 + b ^ 37 = c ^ 37)
        (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
        {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
        (hab : ¬ (a = 0 ∧ b = 0))
        (I : Ideal (𝓞 (CyclotomicField 37 ℚ))) (_hI_ne : I ≠ ⊥)
        (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37),
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (u : 𝓞 (CyclotomicField 37 ℚ)) * γ ^ 37 =
            FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              (CyclotomicField 37 ℚ) a b ζ hab ∧
          (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
            (↑u : 𝓞 (CyclotomicField 37 ℚ)) - 1)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          NumberField.IsCMField.ringOfIntegersComplexConj
            (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) componentId 32 :=
    reflectionOtherDischarge_thirtyseven_of_boundary_and_herbrandRibet
      componentId h_boundary h_herbrand
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_of_thaineAndReflection
      (p := 37) (K := CyclotomicField 37 ℚ)
      componentId thaine reflection
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_caseIAK5UnitCongr_caseIIDescent_noSecondOrder
      cor8_19 caseI_AK5
      (fun hV hSO {_m} D ↦
        FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_unitPower
          (fun {_m'} D' ↦ hgens hV hSO D')
          (fun {_m'} D' ↦ h_unit hV hSO D') D)
      noSecondOrderIrregular

set_option linter.style.longLine false in
/-- **FLT37 from Thaine, Herbrand-Ribet reflection data, direct AK-5
unit congruence, adjacent Case-II quotient generators, and the exact Case-II
quotient-unit p-th-power source.**

This is the generator-only variant of
`fermatLastTheoremFor_thirtyseven_of_thaineHR_caseIAK5UnitCongr_adjacentWashingtonUnitPower_noSecondOrder`:
the Case-II input is just the two anchored span identities used by the descent
formula, plus the exact p-th-power assertion for the unit `ε₁ / ε₂`. -/
theorem
    fermatLastTheoremFor_thirtyseven_of_thaineHR_caseIAK5UnitCongr_adjacentCaseIIGeneratorsUnitPower_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (componentId : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) componentId 32)
    (h_boundary : ¬ componentId.componentNontrivial 36)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
        componentId.componentNontrivial j → (37 : ℤ) ∣ (_root_.bernoulli j).num)
    (caseI_AK5 :
      ∀ {a b c : ℤ}
        (_heq : a ^ 37 + b ^ 37 = c ^ 37)
        (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
        {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
        (hab : ¬ (a = 0 ∧ b = 0))
        (I : Ideal (𝓞 (CyclotomicField 37 ℚ))) (_hI_ne : I ≠ ⊥)
        (_hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37),
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ_ne : γ ≠ 0)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (u : 𝓞 (CyclotomicField 37 ℚ)) * γ ^ 37 =
            FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              (CyclotomicField 37 ℚ) a b ζ hab ∧
          (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
            (↑u : 𝓞 (CyclotomicField 37 ℚ)) - 1)
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m),
        ∃ a₁ b₁ a₂ b₂ : 𝓞 (CyclotomicField 37 ℚ),
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₁ / b₁ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₂ / b₂ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D :
          FLT37.LehmerVandiver.CaseII.CaseIIData37
            (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  let reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) componentId 32 :=
    reflectionOtherDischarge_thirtyseven_of_boundary_and_herbrandRibet
      componentId h_boundary h_herbrand
  let cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32 :=
    cor8_19Bridge_of_thaineAndReflection
      (p := 37) (K := CyclotomicField 37 ℚ)
      componentId thaine reflection
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_caseIAK5UnitCongr_caseIIDescent_noSecondOrder
      cor8_19 caseI_AK5
      (fun hV hSO {_m} D ↦
        FLT37.LehmerVandiver.CaseII.caseII_descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
          (fun {_m'} D' ↦ hgens hV hSO D')
          (fun {_m'} D' ↦ h_unit hV hSO D') D)
      noSecondOrderIrregular

/-- **FLT37 from the exact four non-Bernoulli source surfaces, with the
second-order input explicit.**

Compared with `fermatLastTheoremFor_thirtyseven_of_sources_and_noSecondOrder`,
this theorem exposes the Cor 8.19 input at the narrowed Pollaczek-root level:
under `37 ∣ hPlus`, the canonical real Pollaczek unit
`pollaczekUnitPlusKplus 37 K 32` is a 37-th power. -/
theorem fermatLastTheoremFor_thirtyseven_of_exact_sources_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (h_model_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_sources_and_noSecondOrder
    (cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek)
    caseI_AK5a h_model_ne h_kummer noSecondOrderIrregular

/-- **FLT37 from the exact four non-Bernoulli source surfaces.**

This is the narrowest currently wired public endpoint: the only input supplied
internally is `noSecondOrderIrregularPair_thirtyseven_thirtytwo`, whose sole
remaining work is the user-owned `B_1184` computation.  The four source
arguments stay explicit and are not repackaged as a new bundled hypothesis. -/
theorem fermatLastTheoremFor_thirtyseven_of_exact_sources
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (h_model_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_exact_sources_and_noSecondOrder
    h_pollaczek caseI_AK5a h_model_ne h_kummer
    (noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner kellner)

/-- **FLT37 from the currently narrowest source surfaces, using the shipped
second-order Bernoulli target.**

This is the same composition as
`fermatLastTheoremFor_thirtyseven_of_sources_and_noSecondOrder`,
but with `NoSecondOrderIrregularPair 37 32` supplied by the repository's
current Bernoulli endpoint.  That endpoint is the user-owned `B_1184`
calculation. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_realIdealModel_ne_specificKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (h_model_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_sources_and_noSecondOrder
    cor8_19 caseI_AK5a h_model_ne h_kummer
    (noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner kellner)

/-- **FLT37 from Cor 8.19, AK5a, anchored case-II real descent, and
specific Kummer.**

This is the public composition matching the private final path: the case-II
real-descent source is only the anchored quotient `𝔞 η / 𝔞 η₀`. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_realIdealModel_base_specificKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_AK5a : FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ))
    (h_model_base : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η ≠ zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy
              (zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy))
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    stage2KummerRatioK_of_AK5a_aux caseI_AK5a
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_cor8_19_realIdealModel_base_and_specificKummer
      cor8_19 h_model_base h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseII
    cor8_19 stage2 kellner caseII

/-- **FLT37 from Cor 8.19, case-I class equality, anchored case-II real
descent, and specific Kummer.**

This derives the AK-5a principal-minus source from the smaller
`CaseIClassEqDischarge` target plus the `¬ 37 ∣ h⁺` consequence of Cor 8.19. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_classEq_realIdealModel_base_specificKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_class :
      FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge 37 (CyclotomicField 37 ℚ))
    (h_model_base : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η ≠ zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy
              (zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy))
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 := by
  have h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime
      (FLT37.vandiver37PlusCoprime_of_bridge cor8_19
        FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete)
  have caseI_AK5a : CaseI.AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals_of_classEqDischarge_and_not_dvd_hPlus
      (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide : (37 : ℕ) ≠ 2) h_not_dvd caseI_class
  exact
    fermatLastTheoremFor_thirtyseven_of_cor8_19_AK5a_realIdealModel_base_specificKummer
      cor8_19 caseI_AK5a h_model_base h_kummer kellner

/-- **FLT37 from the exact Pollaczek source, case-I class equality, anchored
case-II real descent, and specific Kummer.**

This is the same reduction as
`fermatLastTheoremFor_thirtyseven_of_cor8_19_classEq_realIdealModel_base_specificKummer`,
but expands the Cor 8.19 input to the canonical Pollaczek-unit p-th-root
statement. -/
theorem fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_classEq_base_specificKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pollaczek :
      (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
        ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
          β ^ 37 =
            FLT37.Sinnott.pollaczekUnitPlusKplus 37
              (CyclotomicField 37 ℚ) 32
              (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37))
    (caseI_class :
      FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge 37 (CyclotomicField 37 ℚ))
    (h_model_base : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η ≠ zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy
              (zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy))
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_cor8_19_classEq_realIdealModel_base_specificKummer
    (cor8_19Bridge_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
      h_pollaczek)
    caseI_class h_model_base h_kummer kellner

set_option maxRecDepth 40000 in
/-- **FLT37 from the factor-ideal class surface plus anchored case-II
sources.**

This variant keeps the case-I input at the concrete factor ideal class level
and uses only the anchored quotient `𝔞 η / 𝔞 η₀` for the case-II real-descent
input. -/
theorem fermatLastTheoremFor_thirtyseven_of_factorIdealClass_base_caseII_sources
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_factor_class :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37) →
        ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
            nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) = 1)
    (h_model_base : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η ≠ zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy
              (zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy))
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.stage2KummerRatioK_of_factorIdeal_class_eq_one
      (K := CyclotomicField 37 ℚ) (by decide : 2 < 37)
      (by decide : (37 : ℕ) ≠ 2) caseI_factor_class
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_cor8_19_realIdealModel_base_and_specificKummer
      cor8_19 h_model_base h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseII
    cor8_19 stage2 kellner caseII

set_option maxRecDepth 40000 in
/-- **FLT37 from the factor-ideal class surface, plus the current case-II
surfaces, using the shipped second-order Bernoulli target.**

This removes the intermediate `Stage2KummerRatioK` and
`CaseIClassEqDischarge` wrappers from the case-I input.  The case-I source is
now the concrete statement that the actual FLT factor ideal `I` in
`(a + ζ b) = I^37` has trivial class. -/
theorem fermatLastTheoremFor_thirtyseven_of_factorIdealClass_and_caseII_sources
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_factor_class :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
        ∀ {ζ : 𝓞 (CyclotomicField 37 ℚ)}, IsPrimitiveRoot ζ 37 →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 (CyclotomicField 37 ℚ))}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 (CyclotomicField 37 ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField 37 ℚ))} :
            Set (𝓞 (CyclotomicField 37 ℚ))) = I ^ 37) →
        ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
            nonZeroDivisors (Ideal (𝓞 (CyclotomicField 37 ℚ)))) = 1)
    (h_model_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal ((𝓞 (CyclotomicField 37 ℚ))⁰)
                (CyclotomicField 37 ℚ))))
    (h_kummer : FLT37.LehmerVandiver.CaseII.AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo) :
    FermatLastTheoremFor 37 := by
  have stage2 : CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    FLT37.LehmerVandiver.CaseI.stage2KummerRatioK_of_factorIdeal_class_eq_one
      (K := CyclotomicField 37 ℚ) (by decide : 2 < 37)
      (by decide : (37 : ℕ) ≠ 2) caseI_factor_class
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
    caseIIBridge_thirtyseven_of_cor8_19_realIdealModel_ne_and_specificKummer
      cor8_19 h_model_ne h_kummer
  exact fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseII
    cor8_19 stage2 kellner caseII

private theorem flt37_evenEigenspace_of_dvd_hPlus_placeholder
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
      ∃ i : ℕ, IsReflectionComponentIndex 37 i ∧ Even i ∧
        eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ) i := by
  have h_decomp :
      StandardEigenspaceDecompositionComplete
        (V := Additive (ClassGroupModP (CyclotomicField 37 ℚ) 37))
        (cyclotomicGalActionInstance (p := 37) (K := CyclotomicField 37 ℚ)) :=
    cyclotomicGalActionInstance_eigenspaceDecompositionComplete
      (p := 37) (K := CyclotomicField 37 ℚ)
      (by simpa using finalReflection_card_zMod_units_isUnit 37)
  have h_V0_trivial :
      eigenspace (V := Additive (ClassGroupModP (CyclotomicField 37 ℚ) 37))
          (cyclotomicGalActionInstance (p := 37) (K := CyclotomicField 37 ℚ)) 0 =
        ⊥ := by
    apply le_antisymm
    · intro v hv
      have hv_zero : v = 0 := by
        by_contra hv_ne
        exact (not_eigenspaceComponentNontrivial_zero 37
          (CyclotomicField 37 ℚ)) ⟨v, hv, hv_ne⟩
      simp [hv_zero]
    · exact bot_le
  exact
    even_eigenspace_nontrivial_of_dvd_hPlus
      (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide : (37 : ℕ) ≠ 2) h_decomp h_V0_trivial

private theorem flt37_dvd_hMinus_of_oddEigenspace_placeholder
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (∃ j : ℕ, IsReflectionComponentIndex 37 j ∧ Odd j ∧
        eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ) j) →
      (37 : ℕ) ∣ hMinus (CyclotomicField 37 ℚ) := by
  intro hodd
  by_contra hnot
  have hfix :
      ∀ v : Additive (ClassGroupModP (CyclotomicField 37 ℚ) 37),
        cyclotomicGalActionInstance
          (p := 37) (K := CyclotomicField 37 ℚ) (-1) v = v :=
    cyclotomicGalActionInstance_neg_one_fixed_of_not_dvd_hMinus
      37 (by decide : (37 : ℕ) ≠ 2) (CyclotomicField 37 ℚ) hnot
  obtain ⟨j, _hj_index, hj_odd, hcomp⟩ := hodd
  exact
    (not_eigenspaceComponentNontrivial_odd_of_neg_one_fixed
      37 (by decide : (37 : ℕ) ≠ 2) (CyclotomicField 37 ℚ)
      hfix hj_odd) hcomp

private def flt37PairedEigenspaceComponentNontrivial
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] (i : ℕ) : Prop :=
  (Even i ∧ eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ) i) ∨
    (Odd i ∧
      eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ)
        (reflectedComponentIndex 37 i))

private theorem reflectedComponentIndex_even_of_odd_aux {i : ℕ} (hi_odd : Odd i) :
    Even (reflectedComponentIndex 37 i) :=
  Nat.Odd.sub_odd (by decide) hi_odd

private theorem reflectedComponentIndex_involutive_aux {i : ℕ}
    (hi : IsReflectionComponentIndex 37 i) :
    reflectedComponentIndex 37 (reflectedComponentIndex 37 i) = i := by
  dsimp [IsReflectionComponentIndex, reflectedComponentIndex] at hi ⊢
  omega

private theorem flt37_pairedEigenspaceReflection
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {i : ℕ} :
    IsReflectionComponentIndex 37 i →
      flt37PairedEigenspaceComponentNontrivial i →
        flt37PairedEigenspaceComponentNontrivial
          (reflectedComponentIndex 37 i) := by
  intro hi hcomp
  rcases hcomp with ⟨hi_even, hcomp_i⟩ | ⟨hi_odd, hcomp_reflect⟩
  · exact Or.inr ⟨reflectedComponentIndex_odd_of_even (by decide : Odd 37) hi hi_even,
      by simpa [reflectedComponentIndex_involutive_aux hi] using hcomp_i⟩
  · exact Or.inl ⟨reflectedComponentIndex_even_of_odd_aux hi_odd, hcomp_reflect⟩

private theorem flt37_pairedEvenEigenspace_of_dvd_hPlus
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
      ∃ i : ℕ, IsReflectionComponentIndex 37 i ∧ Even i ∧
        flt37PairedEigenspaceComponentNontrivial i := by
  intro h_dvd
  obtain ⟨i, hi_index, hi_even, hcomp⟩ := flt37_evenEigenspace_of_dvd_hPlus_placeholder h_dvd
  exact ⟨i, hi_index, hi_even, Or.inl ⟨hi_even, hcomp⟩⟩

private theorem flt37_dvd_hMinus_of_oddPairedEigenspace
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (∃ j : ℕ, IsReflectionComponentIndex 37 j ∧ Odd j ∧
        flt37PairedEigenspaceComponentNontrivial j) →
      (37 : ℕ) ∣ hMinus (CyclotomicField 37 ℚ) := by
  rintro ⟨j, hj_index, hj_odd, hpaired⟩
  have h_eig_j :
      eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ) j := by
    rcases hpaired with ⟨hj_even, _hcomp_j⟩ | ⟨_hj_odd', hcomp_reflect⟩
    · exact absurd hj_odd (Nat.not_odd_iff_even.mpr hj_even)
    · simpa [reflectedComponentIndex_involutive_aux hj_index] using
        weakReflection_componentNontrivial 37 (by decide : Odd 37) (CyclotomicField 37 ℚ)
          (reflectedComponentIndex_isIndex hj_index)
          (reflectedComponentIndex_even_of_odd_aux hj_odd) hcomp_reflect
  exact
    flt37_dvd_hMinus_of_oddEigenspace_placeholder
      ⟨j, hj_index, hj_odd, h_eig_j⟩

private noncomputable def flt37_componentIdentification_placeholder
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ) :=
  ClassGroupComponentIdentification.ofStructural 37 (CyclotomicField 37 ℚ)
    flt37PairedEigenspaceComponentNontrivial
    (h_reflect := fun hi hnon ↦ flt37_pairedEigenspaceReflection hi hnon)
    (h_plus := flt37_pairedEvenEigenspace_of_dvd_hPlus)
    (h_minus := flt37_dvd_hMinus_of_oddPairedEigenspace)

private theorem flt37_evenPairedComponent_to_eigenspace
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {j : ℕ} (hj_even : Even j) :
    (flt37_componentIdentification_placeholder).componentNontrivial j →
      eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ) j := by
  intro hcomp
  change flt37PairedEigenspaceComponentNontrivial j at hcomp
  rcases hcomp with ⟨_hj_even, h_eig⟩ | ⟨hj_odd, _h_reflected⟩
  · exact h_eig
  · exact absurd hj_odd (Nat.not_odd_iff_even.mpr hj_even)

/-- **Kučera/Thaine single-character quotient-torsion source boundary
(named Prop).**

This is the remaining source theorem at `ω^32`: the single-character
Kučera/Thaine annihilator theorem, after reducing the Pollaczek input to the
concrete rank-one Padic quotient torsion statement.

Kept as a named hypothesis (`def … : Prop`), **not** as a project axiom, so the
FLT37 endpoint that consumes it stays explicitly conditional and axiom-clean. -/
def KuceraThaineComponent32Source
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
    (∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
        Submodule.span ℤ_[37]
          ({(FLT37.flt37_pollaczekUnit_padic_eigenspace_class :
              cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                (CyclotomicField 37 ℚ)
                (cyclotomicOmegaPadicChar (p := 37) 32))} : Set _),
      ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0) →
    ¬ (flt37_componentIdentification_placeholder).componentNontrivial 32

private theorem flt37_pairedBoundaryComponent36_trivial
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ flt37PairedEigenspaceComponentNontrivial 36 := by
  intro hcomp
  rcases hcomp with ⟨_h_even, hcomp36⟩ | ⟨h_odd, _hcomp_reflect⟩
  · exact
      (not_eigenspaceComponentNontrivial_zero 37 (CyclotomicField 37 ℚ))
        (eigenspaceComponentNontrivial_zero_of_pred
          37 (CyclotomicField 37 ℚ) hcomp36)
  · exact absurd h_odd (by decide)

private theorem flt37_boundaryComponent36_trivial
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ (flt37_componentIdentification_placeholder).componentNontrivial 36 := by
  change ¬ flt37PairedEigenspaceComponentNontrivial 36
  exact flt37_pairedBoundaryComponent36_trivial

private instance flt37_stickelbergerField_isCyclotomicExtension :
    IsCyclotomicExtension {37 * (37 - 1)} ℚ
      (CyclotomicField (37 * (37 - 1)) ℚ) :=
  CyclotomicField.isCyclotomicExtension (37 * (37 - 1)) ℚ

/-- **Concrete Herbrand/Ribet data attached to a reflected odd eigenspace.**

This packages only the data needed by the already-checked Herbrand API:
an odd p-Sylow component, its Herbrand bridge, and the character-index
normalisation that turns generalized Bernoulli divisibility into
`37 ∣ B_j`. -/
structure FLT37HerbrandRibetReflectedOddData (j : ℕ) where
  /-- The odd unit character attached to the reflected index `37 - j`. -/
  χ : MulChar (ZMod 37)ˣ ℚ
  /-- The p-Sylow class-group component of `ℚ(ζ_{37·36})` carrying `χ`. -/
  C : CyclotomicClassGroupPSylowComponent
    (p := 37) (L := CyclotomicField (37 * (37 - 1)) ℚ)
  /-- The character `χ` is odd. -/
  hχ_odd : IsOddUnitCharacter (p := 37) χ
  /-- The component `C` has character `χ`. -/
  hC : C.character = χ
  /-- The Herbrand bridge attached to the component `C`. -/
  bridge :
    OddComponentHerbrandBridge
      (p := 37) (L := CyclotomicField (37 * (37 - 1)) ℚ)
      (by decide : (37 : ℕ) ≠ 2) χ C
  /-- The component `C` is nontrivial. -/
  hC_nontrivial :
    OddComponentNontrivial
      (p := 37) (L := CyclotomicField (37 * (37 - 1)) ℚ) C
  /-- Character-index normalisation turning generalized Bernoulli divisibility
  into `37 ∣ B_j`. -/
  teichmuller_bridge :
    GeneralizedBernoulliToTeichmullerBridge (p := 37) χ (j - 1)

/-- **Reflected-eigenspace to Herbrand data source boundary (named `def`).**

Weak reflection from the even component to the reflected odd eigenspace is
already checked by `weakReflection_componentNontrivial`.  The remaining source
content is localized to this bridge from the project's `ClassGroupModP`
eigenspace predicate to the p-Sylow Herbrand component API.

Kept as a named hypothesis (`def`), **not** as a project axiom, so the FLT37
endpoint consuming it stays explicitly conditional and axiom-clean.  The source
produces *data* (the Herbrand component package), so it is `Type`-valued. -/
def HerbrandRibetReflectedOddDataSource
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Type :=
    ∀ {j : ℕ}, IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
      eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ)
        (reflectedComponentIndex 37 j) →
        FLT37HerbrandRibetReflectedOddData j

private theorem flt37_herbrandRibet_reflectedOddEigenspace_source
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_hr : HerbrandRibetReflectedOddDataSource)
    {j : ℕ} :
    IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
      eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ)
        (reflectedComponentIndex 37 j) →
        (37 : ℤ) ∣ (_root_.bernoulli j).num := by
  intro hj_index hj_even hj_le hcomp
  let D := h_hr hj_index hj_even hj_le hcomp
  have hgen : GeneralizedBernoulliPDivisible 37 D.χ :=
    generalizedBernoulliPDivisible_of_nontrivial_oddComponent
      (p := 37) (L := CyclotomicField (37 * (37 - 1)) ℚ)
      (by decide : (37 : ℕ) ≠ 2) D.hχ_odd D.C D.hC D.bridge
      D.hC_nontrivial
  have hj_sub_odd : Odd (j - 1) := Nat.Even.sub_odd hj_index.1 hj_even odd_one
  have hj_sub_pos : 0 < j - 1 := by
    rcases hj_even with ⟨k, hk⟩
    have hj_pos : 0 < j := hj_index.1
    omega
  have hj_sub_small : (j - 1) + 1 < 37 - 1 := by omega
  have hordinary :
      OrdinaryBernoulliPDivisible 37 ((j - 1) + 1) :=
    ordinaryBernoulliPDivisible_of_generalizedBernoulliPDivisible
      (p := 37) (by decide : (37 : ℕ) ≠ 2)
      (χ := D.χ) (j := j - 1)
      hj_sub_odd hj_sub_pos hj_sub_small D.teichmuller_bridge hgen
  have hj_sub_add : (j - 1) + 1 = j :=
    Nat.sub_add_cancel hj_index.1
  simpa [OrdinaryBernoulliPDivisible, hj_sub_add] using hordinary

private theorem flt37_herbrandRibet_interior_ne32_source
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_hr : HerbrandRibetReflectedOddDataSource)
    {j : ℕ} :
    IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 → j ≠ 32 →
      (flt37_componentIdentification_placeholder).componentNontrivial j →
        (37 : ℤ) ∣ (_root_.bernoulli j).num := by
  intro hj_index hj_even hj_le _hj_ne hcomp
  have h_eig :
      eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ) j :=
    flt37_evenPairedComponent_to_eigenspace hj_even hcomp
  have h_reflected :
      eigenspaceComponentNontrivial 37 (CyclotomicField 37 ℚ)
        (reflectedComponentIndex 37 j) :=
    weakReflection_componentNontrivial
      37 (by decide : Odd 37) (CyclotomicField 37 ℚ)
      hj_index hj_even h_eig
  exact
    flt37_herbrandRibet_reflectedOddEigenspace_source h_hr
      hj_index hj_even hj_le h_reflected

private theorem flt37_herbrandRibet_interiorComponents
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_hr : HerbrandRibetReflectedOddDataSource) :
    ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
      (flt37_componentIdentification_placeholder).componentNontrivial j →
        (37 : ℤ) ∣ (_root_.bernoulli j).num := by
  intro j hj_index hj_even hj_le hcomp
  by_cases hj32 : j = 32
  · subst hj32
    simpa using thirtyseven_dvd_bernoulli_thirtytwo_num
  · exact
      flt37_herbrandRibet_interior_ne32_source h_hr
        hj_index hj_even hj_le hj32 hcomp

private noncomputable def flt37_refinedThaineBridge_from_sourcePlaceholders
    [Fact (Nat.Prime 37)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_kt : KuceraThaineComponent32Source)
    (h_hr : HerbrandRibetReflectedOddDataSource) :
    FLT37UnitClassBridgeRefined 37 (CyclotomicField 37 ℚ) 32 := by
  let id : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ) :=
    flt37_componentIdentification_placeholder
  refine
    { identification := id
      pollaczekUnitComponent := ?_
      reflectionOtherComponents := ?_ }
  · exact
      (FLT37.thaineSingleCharDischarge37_of_padicEigenspaceQuotient id h_kt).thaine_at_i
  · exact
      (reflectionOtherDischarge_thirtyseven_of_boundary_and_herbrandRibet id
        (by
          change ¬ (flt37_componentIdentification_placeholder).componentNontrivial 36
          exact flt37_boundaryComponent36_trivial)
        (by
          intro j hj_index hj_even hj_le hcomp
          exact
            flt37_herbrandRibet_interiorComponents h_hr
              j hj_index hj_even hj_le (by simpa [id] using hcomp))).reflection_other

private theorem
    flt37_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd_placeholder
    (h_kt : KuceraThaineComponent32Source)
    (h_hr : HerbrandRibetReflectedOddDataSource) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
      ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
        β ^ 37 =
          FLT37.Sinnott.pollaczekUnitPlusKplus 37
            (CyclotomicField 37 ℚ) 32
            (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) :=
  CaseI.flt37_pollaczekUnitPlusKplus_isPthPower_of_refinedThaineBridge
    (flt37_refinedThaineBridge_from_sourcePlaceholders h_kt h_hr)

private theorem flt37_not_dvd_hPlus_placeholder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_kt : KuceraThaineComponent32Source)
    (h_hr : HerbrandRibetReflectedOddDataSource) :
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
  not_dvd_hPlus_thirtyseven_of_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd
    (flt37_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd_placeholder h_kt h_hr)

private theorem flt37_caseI_AK5a_placeholder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_kt : KuceraThaineComponent32Source)
    (h_hr : HerbrandRibetReflectedOddDataSource)
    (h_caseI : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified) :
    FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
      (p := 37) (K := CyclotomicField 37 ℚ) :=
  CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
    (flt37_not_dvd_hPlus_placeholder h_kt h_hr)
    h_caseI

/-- **`FermatLastTheoremFor 37` from the five source boundaries** (axiom-clean,
explicitly conditional).

The five remaining non-Bernoulli mathematical surfaces are taken as explicit
named hypotheses — **not** project axioms — so this theorem depends only on the
standard mathlib axioms `propext`, `Classical.choice`, `Quot.sound`:

- `h_kuceraThaine` (`KuceraThaineComponent32Source`): the single-character
  Kučera/Thaine rank-one annihilator at `ω^32`.
- `h_herbrandRibet` (`HerbrandRibetReflectedOddDataSource`): the reflected odd
  eigenspace → Herbrand p-Sylow component data.
- `h_caseI` (`CaseIAntiKummerLKUnramified`): Case-I σ-anti Kummer
  unramifiedness.
- `h_caseII_gens` (`WashingtonCaseIIAdjacentFixedGenerators37Source`):
  Washington §9.4 adjacent fixed integral generators.
- `h_caseII_unit` (`WashingtonCaseIIExactQuotientUnitPower37Source`):
  Washington §9.4 exact quotient-unit `37`th power.

Plus `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` (the FLT37
second-order Bernoulli input, itself reducible to the `B_1184` computation). -/
theorem fermatLastTheoremFor_thirtyseven_of_source_boundaries_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_kuceraThaine : KuceraThaineComponent32Source)
    (h_herbrandRibet : HerbrandRibetReflectedOddDataSource)
    (h_caseI : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (h_caseII_gens : FLT37.LehmerVandiver.CaseII.WashingtonCaseIIAdjacentFixedGenerators37Source)
    (h_caseII_unit : FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_exact_pollaczek_AK5a_caseIIDescent_noSecondOrder
    (flt37_pollaczekUnitPlusKplus_isPthPower_under_hPlus_dvd_placeholder
      h_kuceraThaine h_herbrandRibet)
    (flt37_caseI_AK5a_placeholder h_kuceraThaine h_herbrandRibet h_caseI)
    (fun hV hSO {_m} D ↦
      FLT37.LehmerVandiver.CaseII.caseII_descent_step_under_vandiver37
        h_caseII_gens h_caseII_unit hV hSO D)
    noSecondOrderIrregular

end BernoulliRegular

end

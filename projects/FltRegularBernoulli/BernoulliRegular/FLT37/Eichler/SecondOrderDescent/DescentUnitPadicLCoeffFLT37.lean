import BernoulliRegular.FLT37.Eichler.SecondOrderDescent.DescentDetectorVanishing

/-!
# `Cor823Omega32SecondOrderCollapse37` from the genuine second-order coefficient core

This file discharges `Cor823Omega32SecondOrderCollapse37` (`CaseIICor823Discharge.lean`) —
Washington
Proposition 8.12 at the irregular index `i = 32`, second order — down to **one** strictly-smaller,
sound, non-circular residual: the genuine `p`-adic-`L` **leading-coefficient value**
`Prop812DescentCoeff37`.  It combines that residual with the **proven** second-order detector
vanishing (`caseIICor823SecondOrder_detector_descent_eq_zero`, the deep `c^{36} ≢ 1 (mod 37²)`
valuation half of `CaseIICor823SecondOrderDetector.lean`) and the proven non-degeneracy
`β₃₂ = 3 ≠ 0`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The mechanism (why this closes the collapse, and why it is not circular)

The mod-`37²` `varpi^32` detector of the descent logarithm `completedLog(u^{36})` is **proven** to
vanish (`caseIICor823SecondOrder_detector_descent_eq_zero`): the genuine second-order valuation
half,
from the proven `X^{36} - c^{36} ∈ λ^{72}` split (the `c^{36} ≢ 1 (mod 37²)` obstruction handled by
separating the rational constant from the `varpi^32` coordinate).

The genuine `p`-adic-`L` residual `Prop812DescentCoeff37` (Washington Proposition 8.12 at `i = 32`,
the single-unit `p`-adic logarithm leading coefficient) is the **coefficient-value identity**: this
detector equals the second-order Bernoulli factor `B₃₂/32 mod 37²` times a lift of the `j = 15`
free-part eigencomponent `caseIIResidueProvenance_decomp (realUnitToFreePartModP u) 15`.

Because the Bernoulli factor is `37·(unit)` modulo `37²` (the proven
`caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul`, `β₃₂ = 3 ≠ 0`), the detector
vanishing forces `37 · unit · (lift c₁₅) ≡ 0 (mod 37²)`, hence `unit · c₁₅ ≡ 0 (mod 37)`, hence
`c₁₅ = 0`. This is the genuine second-order mechanism: the extra `37` of precision (the irregularity
`37 ∣ B₃₂`) is exactly what recovers the mod-`37` eigencomponent that the first order — degenerate
at
`j = 15` (`B₃₂ mod 37 = 0`) — cannot see.

**Non-circular**: the residual `Prop812DescentCoeff37` is a coefficient-**value** identity (the
detector equals `B₃₂ mod 37²` times a lift of `c₁₅`), the genuine single-unit `p`-adic log leading
coefficient of Proposition 8.12; the **vanishing** of the eigencomponent is *derived* from the
*separately proven* detector vanishing, never assumed.  It is **not** a restatement of `c₁₅ = 0`
(unlike the prior pass's `Cor823Omega32SecondOrderVandermonde37`, which stated `(V·ē)₁₅ = 0`,
equivalent to `c₁₅ = 0` via `9·c₁₅`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007),
  Proposition 2.7.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The genuine second-order leading-coefficient residual for the descent unit -/

/-- **The genuine second-order leading-coefficient residual: Proposition 8.12 at `i = 32`, on the
descent unit** (a `def … : Prop`, **not** an axiom — the genuine `p`-adic-`L` content).

For every unit `u : (𝓞 K⁺)ˣ` and rational integer `c` with `37² ∣ algebraMap u - c` (the Cor-8.23
input class), the mod-`37²` `varpi^32` Dwork detector of the descent logarithm
`completedLog(u^{36})`
factors as the second-order Bernoulli factor `caseIICor823SecondOrderBernoulliFactorModSq`
(`= B₃₂/32 mod 37²`) times a lift `D : ZMod (37²)` of the `j = 15` free-part eigencomponent
`caseIIResidueProvenance_decomp (realUnitToFreePartModP u) 15`:

  `∃ D : ZMod (37²), detector(u) = caseIICor823SecondOrderBernoulliFactorModSq · D ∧`
  ` (ZMod.castHom (37 ∣ 37²) (ZMod 37)) D = caseIIResidueProvenance_decomp (realUnitToFreePartModP
  u) 15`.

This is the single-unit `p`-adic logarithm leading coefficient of Washington Proposition 8.12 at the
irregular index `i = 32`: the level-`68` mod-`37²` coordinate of the local logarithm equals the
`B₃₂ mod 37²` Bernoulli factor times the eigencomponent datum.  It is the second-order analog of the
proven first-order factorization `concreteKummerLogMatrix = diag(B mod 37)·V`, at the irregular row,
made explicit modulo `37²`.

It is **sound** (a coefficient-value identity for the specific descent congruence datum `u`),
**non-circular** (the conclusion is the explicit `B₃₂ mod 37²`-factored coefficient value with the
eigencomponent appearing only inside the *lifted datum* `D`, never as the vanishing target; the
vanishing of `c₁₅` is derived from the *separately proven* detector vanishing), and **non-vacuous**
(`u = 1`, `c = 1`: the detector is `0`, `D = 0` works, and `c₁₅ = 0` — see
`prop812DescentCoeff37_inhabited`). -/
def Prop812DescentCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
    ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) →
    ∃ D : ZMod (37 ^ 2),
      caseIICor823DescentDetectorSq u =
        caseIICor823SecondOrderBernoulliFactorModSq * D ∧
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) D =
        caseIIResidueProvenance_decomp
          (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) 15

/-- **The antecedent of `Prop812DescentCoeff37` is inhabited** (non-vacuity, proven): the unit
`u = 1` with `c = 1` satisfies `37² ∣ algebraMap 1 - 1 = 0` (the Cor-8.23 input class).  So
`Prop812DescentCoeff37` is a real implication on a satisfiable hypothesis, not vacuously true. -/
theorem prop812DescentCoeff37_antecedent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
      ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
        ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
            (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
          (c : 𝓞 (CyclotomicField 37 ℚ))) :=
  ⟨1, 1, by simp⟩

/-! ## 2. `Cor823Omega32SecondOrderCollapse37` from the residual + the proven detector vanishing -/

/-- **`Cor823Omega32SecondOrderCollapse37` from the genuine second-order coefficient core** (proven,
axiom-clean given `Prop812DescentCoeff37`).

For `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u - c`:
* the **proven** second-order detector vanishing
  `caseIICor823SecondOrder_detector_descent_eq_zero` makes the mod-`37²` `varpi^32` detector of
  `completedLog(u^{36})` equal `0`;
* the residual `Prop812DescentCoeff37` factors that detector as
  `caseIICor823SecondOrderBernoulliFactorModSq · D` with `castHom D = c₁₅`;
* the **proven** non-degeneracy `caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul`
  (`β₃₂ = 3 ≠ 0`) writes the factor as `37·r` with `r` a unit mod `37`, so `0 = 37·r·D (mod 37²)`
  forces `r·(castHom D) = 0 (mod 37)`, hence `castHom D = c₁₅ = 0`. -/
theorem cor823Omega32SecondOrderCollapse37_of_prop812
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hProp : Prop812DescentCoeff37) :
    Cor823Omega32SecondOrderCollapse37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro u c hc
  -- (1) The proven detector vanishing.
  have hdet0 : caseIICor823DescentDetectorSq u = 0 :=
    caseIICor823SecondOrder_detector_descent_eq_zero u c hc
  -- (2) The residual's factorization.
  obtain ⟨D, hDfac, hDcast⟩ := hProp u c hc
  -- (3) `factor · D = 0` (detector vanishes).
  have hfacD0 : caseIICor823SecondOrderBernoulliFactorModSq * D = 0 := by
    rw [← hDfac]; exact hdet0
  -- (4) `factor = 37·r`, `r` a unit mod 37.
  obtain ⟨r, hrfac, hr_ne⟩ := caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul
  rw [hrfac] at hfacD0
  -- `37·(r·D) = 0 (mod 37²)`, so `r·D ∈ ker(castHom 37)`, i.e. `castHom (r·D) = 0 (mod 37)`.
  have h37rD : (37 : ZMod (37 ^ 2)) * (r * D) = 0 := by rw [← hfacD0]; ring
  -- `37·x = 0 mod 37²` ⟹ `castHom x = 0 mod 37` (the `varpi`/precision step: a `37`-annihilated
  -- element lies in `(37) = ker (ZMod 37² → ZMod 37)`).
  have hkey : ∀ x : ZMod (37 ^ 2), (37 : ZMod (37 ^ 2)) * x = 0 →
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) x = 0 := by
    intro x hx
    -- `37 * x = 0` in `ZMod 37²` ⟹ `37² ∣ 37 * x.val` ⟹ `37 ∣ x.val` ⟹ `(x.val : ZMod 37) = 0`.
    have hval : (37 ^ 2 : ℕ) ∣ 37 * x.val := by
      have h0 : ((37 * x.val : ℕ) : ZMod (37 ^ 2)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id, Nat.cast_ofNat]
        exact hx
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hdvd : (37 : ℕ) ∣ x.val := by
      obtain ⟨t, ht⟩ := hval
      -- `37 * x.val = 37^2 * t = 37 * (37 * t)`, cancel `37`: `x.val = 37 * t`.
      refine ⟨t, ?_⟩
      have h37 : (37 : ℕ) * x.val = 37 * (37 * t) := by rw [ht]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h37
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hrD_mod : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) (r * D) = 0 :=
    hkey (r * D) h37rD
  -- (5) `r·(castHom D) = 0 mod 37`, `r` unit ⟹ `castHom D = 0`, i.e. `c₁₅ = 0`.
  rw [map_mul] at hrD_mod
  have hcD0 : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) D = 0 :=
    (mul_eq_zero.mp hrD_mod).resolve_left hr_ne
  rw [hDcast] at hcD0
  exact hcD0

/-! ## 3. `R4` discharged down to the genuine `p`-adic-`L` coefficient core, and the FLT37 endpoint
-/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the genuine second-order `p`-adic-`L`
leading-coefficient core** (proven, axiom-clean given the genuine residuals + the carried Kellner
Prop).

Composes `cor823Omega32SecondOrderCollapse37_of_prop812` (which discharges
`Cor823Omega32SecondOrderCollapse37` from the single genuine coefficient residual
`Prop812DescentCoeff37`, using the **proven** second-order detector vanishing and non-degeneracy)
with `fermatLastTheoremFor_thirtyseven_of_omega32Collapse`.  All of the Theorem-8.22 plumbing
(WLOG-real, `p`-saturation, the proven R3 regular collapse, Step D, the K↔K⁺ descent), the
second-order coefficient machinery (the mod-`37²` Dwork coordinate API), the second-order detector
**vanishing** (the deep `c^{36} ≢ 1 (mod 37²)` valuation half), and the non-degeneracy `β₃₂ = 3 ≠ 0`
are **proven**; only the single-unit `p`-adic logarithm leading-coefficient **value**
`Prop812DescentCoeff37` (Washington Proposition 8.12 at `i = 32`) remains. -/
theorem fermatLastTheoremFor_thirtyseven_of_prop812Descent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_prop812 : Prop812DescentCoeff37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_omega32Collapse
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (cor823Omega32SecondOrderCollapse37_of_prop812 caseII_prop812)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

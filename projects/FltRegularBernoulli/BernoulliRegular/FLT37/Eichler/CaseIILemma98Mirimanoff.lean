import BernoulliRegular.FLT37.Eichler.CaseIIXiReality
import BernoulliRegular.FLT37.Eichler.CaseIILemma98DescentSum

/-!
# Discharge of `Lemma98MirimanoffPthPower37` to Washington's step-5 `ρ_a`-reality (`p = 37`)

This file completes the reduction of the residual `Lemma98MirimanoffPthPower37`
(`CaseIILemma98DescentSum.lean`) — Washington Lemma 9.8 steps 5–8, the Kummer–Mirimanoff
congruence —
to the **single** genuine analytic core `MirimanoffRhoReality37` (`CaseIIMirimanoffTelescope.lean`),
Washington's step-5 `ρ_a`-reality ratio congruence.

## Status of the chain

* **Lemma 8.1** (the `ξ_a` ratio identity `(ζ^a-ζ^j)/(1-ζ^{a+j}) = -ξ_{a-j}/ξ_{a+j}`):
  **PROVEN** (`xi_ratio_identity`, `CaseIILemma81.lean`).
* **Step 6** (ratio `p`-th power ⟹ equal `ind₃₇`): **PROVEN** (`caseII_xi_ratio_ind`).
* **Step 7** (the `ξ_b` telescoping, all `ξ_b` are `37`-th powers mod `𝔩`): **PROVEN**
  (`caseII_xiIndZMod_eq_zero`, via the `ZMod 37` orbit lemma `caseII_telescope_const`).
* **Step 8** (Galois/reality descent: `E₃₂ = (∏ ξ_b^{b⁴})²`, so `E₃₂` is a `37`-th power mod `𝔩`):
  **PROVEN** (`caseII_pollaczekUnitPlus_eq_xiProd_sq`, `caseII_E32_isPthPower_of_rhoReality`), using
  the reality `σ(ξ_b) = ξ_b` (`caseII_unitsComplexConj_xiUnit`, the totally-real Lemma 8.1 units).
* **Step 5** (the `ρ_a`-reality ratio congruence): isolated as `MirimanoffRhoReality37` (the
  smallest
  genuine residual — the analytic heart that needs `(ω+ζ^aθ)/(1-ζ^a) = ρ_a^p·unit` with `ρ_a` real
  because `p ∤ h⁺`, plus the cyclic-group congruence `ℓ-1 = kp`, `k` even).

So the **only** undischarged content is `MirimanoffRhoRealityProducer37` (step 5, as a producer over
the Case-II descent), and `Lemma98MirimanoffPthPower37` follows from it
(`caseII_lemma98Mirimanoff_of_rhoReality`).

## Non-vacuity (tying the residual to the proven `Q₃₂⁴ ≢ 1`)

`caseII_E32_isPthPower_of_rhoReality` shows `MirimanoffRhoReality37 j` (`j ≠ 0`) forces `E₃₂` to
be a
`37`-th power mod `lv149`, which **contradicts** the proven `caseIIThm95_engine_runs` (`Q₃₂⁴ ≢ 1`).
Hence `MirimanoffRhoReality37 j` is **false** for `j ≠ 0` — so the producer residual genuinely
asserts
that no nontrivial conjugate factor `x + ζ^j y ∈ lv149` (`j ≠ 0`) can occur (Washington's `j = 0`).
It is neither vacuously true (its `ρ_a`-reality conclusion is a real constraint) nor trivially false
(it is exactly the negation of the descent producing a nontrivial factor).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.1 (Lemma 8.1), §9.1–9.2
  (Lemma 9.8, pp. 178–179).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-! ## The step-5 producer residual over the Case-II descent -/

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.8 step-5 `ρ_a`-reality producer for `p = 37`** (a `def … : Prop`,
**not** an
axiom) — the **smallest genuine analytic core** of the Mirimanoff congruence.

For every Case-II descent instance with a *nontrivial* conjugate factor `D.x + η·D.y ∈ lv149`
(`η ∈ μ₃₇`, `η ≠ 1`, with `ℓ ∤ D.x, D.y`), and for the index `i` realising `η = ζ^i`
(`ζ = zeta 37 ℚ K`), the step-5 ratio congruence `MirimanoffRhoReality37 (i : ZMod 37)` holds: for
every `b ≢ 0, -2i (mod 37)`, the real cyclotomic-unit ratio `ξ_{b+2i}·ξ_b^{-1}` is a `37`-th power
mod `lv149`.

This is the `ρ_a`-reality input of Washington Lemma 9.8 (pp. 178–179): from
`(ω+ζ^aθ)/(1-ζ^a) = ρ_a^p·unit` (with `ρ_a` **real** because `p ∤ h⁺`) and the cyclic-group
congruence (`ℓ-1 = kp`, `k` even, `ω ≡ -ζ^iθ`).  Everything that Washington derives **from** it —
the §8.1 ratio-unit identification (Lemma 8.1, proven), the `ξ_b` telescoping (step 7, proven), and
the σ-collapse `E₃₂ = (∏ξ_b^{b⁴})²` (step 8, proven) — is already formalised; this is the only
remaining input. -/
def MirimanoffRhoRealityProducer37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)},
    η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) →
    η ≠ 1 →
    D.x ∉ lv149 → D.y ∉ lv149 →
    D.x + η * D.y ∈ lv149 →
    ∀ i : ℕ, ((zetaU 37 (CyclotomicField 37 ℚ) : 𝓞 (CyclotomicField 37 ℚ)) ^ i = η) →
      MirimanoffRhoReality37 (i : ZMod 37)

/-! ## Discharge of `Lemma98MirimanoffPthPower37` -/

open FLT37.LehmerVandiver.CaseII in
/-- **`Lemma98MirimanoffPthPower37` from the step-5 producer** (proven, axiom-clean *given*
`MirimanoffRhoRealityProducer37`).

For a nontrivial conjugate factor `D.x + η·D.y ∈ lv149` (`η ≠ 1`, `ℓ ∤ x, y`), write `η = ζ^i`
(`i < 37`, `i ≠ 0` since `η ≠ 1`); the producer gives `MirimanoffRhoReality37 (i : ZMod 37)`, and
`caseII_E32_isPthPower_of_rhoReality` (the proven telescoping + σ-collapse) makes `E₃₂` a `37`-th
power mod `lv149`. -/
theorem caseII_lemma98Mirimanoff_of_rhoReality
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_producer : MirimanoffRhoRealityProducer37) :
    Lemma98MirimanoffPthPower37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  unfold MirimanoffRhoRealityProducer37 at h_producer
  intro hV hSO m D η hη_mem hη_ne hx hy hsum
  -- `η^37 = 1`, so `η = ζ^i` for some `i < 37`.
  have hη_pow : η ^ 37 = 1 := by
    rw [mem_nthRootsFinset (by decide : 0 < 37)] at hη_mem
    exact hη_mem
  obtain ⟨i, hi_lt, hi_eq⟩ :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hη_pow
  -- `i ≠ 0` (else `η = ζ^0 = 1`), so `(i : ZMod 37) ≠ 0`.
  have hi_ne : (i : ZMod 37) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have : i = 0 := by omega
    rw [this, pow_zero] at hi_eq
    exact hη_ne hi_eq.symm
  -- The producer gives `MirimanoffRhoReality37 (i : ZMod 37)`.
  have hρ : MirimanoffRhoReality37 (i : ZMod 37) :=
    h_producer hV hSO D hη_mem hη_ne hx hy hsum i hi_eq
  -- The proven telescoping + σ-collapse make `E₃₂` a `37`-th power mod `lv149`.
  exact caseII_E32_isPthPower_of_rhoReality hρ hi_ne

/-! ## Capstone: the genuine Washington Lemma 9.8 from the single producer residual

Combining the discharge above with the proven contradiction half `caseIIThm95_engine_runs`
(`Q₃₂⁴ ≢ 1`), the full Washington Lemma 9.8 (`ℓ ∣ z ⟹ ℓ ∣ (ω+θ)`, i.e. the special index `j = 0`)
holds *given only* the single step-5 producer residual `MirimanoffRhoRealityProducer37`. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.8 for `p = 37`, from the single step-5 residual** (proven, axiom-clean
*given* `MirimanoffRhoRealityProducer37`).

With the standing `ℓ ∣ z` (Lemma 9.7) and Lemma 9.6 (`ℓ ∤ x, y`), the descended sum `x + y ∈ lv149`
(`ℓ ∣ (ω+θ)`, Washington's `j = 0`).  This is `caseII_lemma98_x_add_y_mem_of_dvd_z` fed by the
discharge `caseII_lemma98Mirimanoff_of_rhoReality`; the `j ≠ 0` case is refuted because the producer
forces `E₃₂` to be a `37`-th power mod `lv149`, contradicting the proven
`caseIIThm95_engine_runs`. -/
theorem caseII_lemma98_x_add_y_mem_of_producer
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_producer : MirimanoffRhoRealityProducer37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.x + D.y ∈ lv149 :=
  caseII_lemma98_x_add_y_mem_of_dvd_z
    (caseII_lemma98Mirimanoff_of_rhoReality h_producer) hV hSO D hz hxl hyl

/-- **Non-vacuity, made explicit.**  `MirimanoffRhoReality37 j` with `j ≠ 0` is **false**: it would
make `E₃₂` a `37`-th power mod `lv149` (`caseII_E32_isPthPower_of_rhoReality`), contradicting the
proven `caseIIThm95_engine_runs` (`Q₃₂⁴ ≢ 1`).  Hence the residual `MirimanoffRhoReality37 j`
(`j ≠ 0`)
is a genuine constraint — neither vacuously true nor trivially false. -/
theorem caseII_not_rhoReality_of_ne_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {j : ZMod 37} (hj : j ≠ 0) : ¬ MirimanoffRhoReality37 j := fun hρ =>
  caseIIThm95_engine_runs (caseII_E32_isPthPower_of_rhoReality hρ hj)

end BernoulliRegular.FLT37.Eichler

end

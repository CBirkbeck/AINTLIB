import BernoulliRegular.FLT37.Eichler.CaseII.FreeContent.DescendedContentIsPContent
import BernoulliRegular.FLT37.Eichler.Reduction.ConjugateResidueEqnsFromR3
import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.GammaRatioLocalPower
import BernoulliRegular.FLT37.Eichler.Saturation.SingleIndexExpansionFromResidueEqns

/-!
# [FLT37-CASEII-MODULO-KELLNER] The cleanest FLT37 Case-II endpoint and the minimal residual

This file assembles the cleanest available FLT37 endpoint built on the **correct factor-count
frame** (`fermatLastTheoremFor_thirtyseven_of_pContentDescent`,
`CaseIIFreeContentNonPContent.lean`),
pushing every component that is dischargeable from the already-proven pieces, and pinning the
**exact minimal residual** that remains.  It imports only — it does **not** modify any existing
file.
No `sorry`,
no `axiom`.

## What is dischargeable here (genuine, axiom-clean Lean — proven below)

* **`Cor815SingleIndexExpansion37` is unconditionally PROVEN.**
  `caseII_corollary815_singleIndexExpansion37_proven` is the application
  `caseII_corollary815_singleIndexExpansion_of_residueEqns` to
  `caseIISigmaAntiDescent_residueEqns_proven`:
  Washington Corollary 8.15's single-index expansion `ε₁/ε₂ = E₃₂^{d}·α^{37}` of the Case-II descent
  unit, from the **proven, unconditional** half-range conjugate residue equations (R3 route).  This
  removes the single-index expansion from the residual set entirely.

* **Instance-wise Assumption II in the `ℓ ∣ z` frame is PROVEN.**
  `caseII_descentUnit_isPow_of_dvdZ_instance`: for *any* descent-equation-shaped instance
  `ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·((ζ−1)^m·z')³⁷` with the Lemma-9.6/9.7 membership facts `x' ∉ 𝔩`,
  `z' ∈ 𝔩` (the datum fields of the `ℓ ∣ z` frame `RealCaseIIDvdZData37`), the descent unit `ε₁/ε₂`
  is a **genuine global `37`-th power** `ε'^37`.  This is the proven (banked) single-index expansion
  composed with the **per-instance** direct local power `caseII_lemma98LocalPower37_directResidue`
(no false universal `Lemma98LocalPower37`, no §9.1 identification residual R4(i), no `p`-adic-`L`).
  This is the **sound** discharge of Assumption II's descent-unit content in the frame where it is
  available — exactly the frame `CaseIISection91PContentExtractionData37`'s data lives in.

* **The non-`p`-content gap clause is PROVEN from the genuine-integral-unit anchor.**
  `caseII_pContentClause_of_genuineUnit_anchor`: the §9.1 anchor equation
  `algebraMap(x+y) = algebraMap(u₀)·Λ^e·ρ₀³⁷` with `u₀ : (𝓞 K)ˣ` a **genuine algebraic-integer
  unit** (Washington's anchor unit *is* integral — it is the ratio of integers `(x+y)/(Λ^e·ρ₀³⁷)`
  whose ideal balances, `ρ₀ ∈ 𝓞 K` an anchor generator), together with `algebraMap z' = ρ₀²` and the
  anchor-support `(z') = 𝔞₀ᵏ` (which gives `¬𝔭 ∣ z'`), forces the descended `(ζ−1)`-content
  `2·(2e−1) = 37·(2m)` — the `p`-content clause `∃ m'', 2·(2e−1) = 37·(m''+1)`.  Via the proven
`caseII_descended_content_eq` (`2e = 37m+1`, the sharp anchor valuation).  So the ad-hoc existential
  `p`-content clause of `CaseIISection91PContentExtractionData37` is **derivable** — it need not be
  asserted: it is the genuine-unit anchor's consequence.

## The genuine-unit `ℓ ∣ z` extraction data, and the reduction (PROVEN)

`CaseIISection91DvdZGenuineUnitExtractionData37` is `CaseIISection91DvdZExtractionData37` with the
anchor unit `η₀` **strengthened** to a genuine algebraic-integer unit `η₀ = algebraMap u₀`
(`u₀ : (𝓞 K)ˣ`) — the form Washington's construction actually outputs — and the ad-hoc `p`-content
existential clause **dropped** (it is no longer needed: it follows).  The reduction
`caseIISection91PContentExtractionData37_of_dvdZGenuineUnit` proves

  `CaseIISection91DvdZGenuineUnitExtractionData37 → CaseIISection91PContentExtractionData37`,

so the §9.1-content residual is the *cleaner* genuine-integral-unit form.  Feeding it through the
proven `fermatLastTheoremFor_thirtyseven_of_pContentDescent` gives the endpoint
`fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction`.

## The minimal residual set (HONEST — soundness-first; not faked)

`FermatLastTheoremFor 37` is **not** proven outright here.  After the discharges above, the
endpoint `fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction` rests on exactly:

1. **`h_data : CaseIISection91DvdZGenuineUnitExtractionData37`** — the genuine remaining R2 content:
   Washington's §9.1 Theorem 9.4 descent **construction** producing, for every real `ℓ ∣ z` datum,
   (a) the anchor equation `x+y = algebraMap(u₀)·Λ^e·ρ₀³⁷` with the *genuine-integral-unit* anchor
(the `B₀`-principalization on `x+y`; for irregular `37` the anchor ideal `𝔞₀` is **not** principal
— its conjugate norm `𝔞₀·σ𝔞₀` is, via `37 ∤ h⁺`, the proven `caseII_anchorPow_conjNorm_real_span`,
giving the genuine real generator at the doubled measure that the free-content frame consumes), (b)
   **Assumption II** `η_a = u³⁷·η_b` for the two §9.1 factor units (the unit ratio `η_a/η_b` is the
   descent unit `ε₁/ε₂`, whose `37`-th-power-ness in the `ℓ ∣ z` frame is the **proven**
   `caseII_descentUnit_isPow_of_dvdZ_instance` once the factor equations are rewritten in
   descent-equation shape — the remaining content is that rewriting + the conjugate-norm building
   blocks), and (c) the two sharp `𝔭`-valuation invariants `hxy'`/`hdenom'` + anchor-support.  **No
   producer exists** in the repo; this is the structural heart of the classical cyclotomic FLT
descent.  It is **not** the obstructed `∃ m' < m` linear measure, **not** the false universal local
   power, **not** the RepointObstruction §9.1 identification — those are all bypassed.

2. **`h_cop`** — the per-datum coprimality `IsCoprime ((x')) ((y'))` of the promoted Fermat
variables.
The **universal** "every free-content datum is coprime" is provably FALSE (scale a base datum by a
   rational prime `≠ 37`), and there is **no** coprimality-propagation lemma; so it is a genuine
   threaded hypothesis at every descent level.  Kept, minimized.

3. **`h_lemma96`** — Washington Lemma 9.6 (`149 ∤ x` for the integer Fermat triple with `37 ∤ x`).
   Not a pure mod-`149` fact (the residue map `furtwangler_37_149` is consistent with `149 ∣ x`); it
is vacuously true (no nontrivial Fermat-`37` triple) but **only via** the FLT37 conclusion itself,
so it cannot be discharged non-circularly without Washington's auxiliary-prime argument.  Carried.

4. **`noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32`** — the carried Kellner input
   (`37³ ∤ B₁₁₈₄`, Kellner Prop 2.7), **not** a leaf to discharge.

So the milestone "FLT37 modulo Kellner with *everything else* proven" is **not** reached: it would
require discharging `h_data` (R2), `h_cop`, and `h_lemma96`, none of which is dischargeable from the
present pieces (`h_data` is the open construction; `h_cop`/`h_lemma96` are sound-but-not-provable
threaded inputs).  The honest reduction is the four-input endpoint above, with the §9.1 content in
its
**cleanest genuine-integral-unit form** and the single-index expansion / instance-wise Assumption II
/
`p`-content clause all **discharged**.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), Lemma 9.6
  (p. 179), Lemma 9.7, Lemma 9.8 (p. 180), Lemma 9.9 (pp. 180–181), Corollary 8.15 (p. 153),
  Corollary 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. `Cor815SingleIndexExpansion37` is unconditionally PROVEN (banked) -/

/-- **Washington Corollary 8.15's single-index expansion is unconditionally PROVEN** (axiom-clean).

`Cor815SingleIndexExpansion37` — the single-index cyclotomic-unit expansion
`ε₁/ε₂ = E₃₂^{d}·α^{37}` of the Case-II descent unit — is the composition of the proven
single-index discharge `caseII_corollary815_singleIndexExpansion_of_residueEqns` with the **proven,
unconditional** half-range conjugate residue equations `caseIISigmaAntiDescent_residueEqns_proven`
(R3 route).  This removes the single-index expansion from the FLT37 Case-II residual set. -/
theorem caseII_corollary815_singleIndexExpansion37_proven :
    Cor815SingleIndexExpansion37 :=
  caseII_corollary815_singleIndexExpansion_of_residueEqns
    caseIISigmaAntiDescent_residueEqns_proven

/-! ## 2. Instance-wise Assumption II in the `ℓ ∣ z` frame (PROVEN, sound) -/

/-- **The descent unit `ε₁/ε₂` is a genuine global `37`-th power, in the `ℓ ∣ z` frame** (proven,
axiom-clean — **no** false universal local power, **no** §9.1 identification residual).

For any Case-II descent-equation-shaped instance
`ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·((ζ−1)^m·z')³⁷` with the standing Washington membership facts `x' ∉ 𝔩`
(Lemma 9.6), `z' ∈ 𝔩` (Lemma 9.7) — exactly the datum fields of the `ℓ ∣ z` frame
`RealCaseIIDvdZData37` — the descent unit `ε₁/ε₂` is a genuine global `37`-th power `ε'^37`.

This is the **instance-wise Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`
conclusion, per instance): the proven single-index expansion
`caseII_corollary815_singleIndexExpansion37_proven` supplies `ε₁/ε₂ = E₃₂^{d}·α^{37}`, the
**per-instance** direct local power `caseII_lemma98LocalPower37_directResidue` (from `x' ∉ 𝔩`,
`z' ∈ 𝔩`) supplies `IsPthPowerModPrime 37 𝔩 (ε₁/ε₂)`, and the proven single-index collapse §4
(`caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`, operative core `ind₃₇ E₃₂ ≠ 0`) upgrades
local to global.

Crucially this uses the local power at the **specific** instance (where the `ℓ`-membership fields
are available), never the bare universal `Lemma98LocalPower37` (false on the free-unit telescope,
B2 `CASEII-LEMMA98-LOCALPOWER`). -/
theorem caseII_descentUnit_isPow_of_dvdZ_instance
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hx_p : ¬ (D.hζ.toInteger - 1) ∣ x') (hy_p : ¬ (D.hζ.toInteger - 1) ∣ y')
    (hz_p : ¬ (D.hζ.toInteger - 1) ∣ z')
    (heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37)
    (hxl : x' ∉ lv149) (hzl : z' ∈ lv149) :
    ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37 := by
  obtain ⟨d, α, hexp⟩ :=
    caseII_corollary815_singleIndexExpansion37_proven hV hSO D hx_p hy_p hz_p heq
  have hlp := caseII_lemma98LocalPower37_directResidue D (e := m) hxl hzl heq
  exact caseIIThm95_descentUnit_isPow_of_singleIndexExpansion (ε₁ / ε₂) d α hexp hlp

/-! ## 3. The `p`-content clause from the genuine-integral-unit anchor (PROVEN) -/

/-- **The non-`p`-content-gap clause from the genuine-integral-unit anchor** (proven, axiom-clean).

For a real Case-II datum `D` at level `m`, the §9.1 anchor equation
`algebraMap(x+y) = algebraMap(u₀)·Λ^e·ρ₀³⁷` (`Λ = (1−ζ)(1−ζ³⁶)`, `ζ = zeta_spec`, `u₀ : (𝓞 K)ˣ` a
**genuine algebraic-integer unit**) together with `algebraMap z' = ρ₀²` and the anchor-support
`(z') = 𝔞₀ᵏ` (`k ≥ 1`, which gives `¬𝔭 ∣ z'`) force the §9.1-descended `(ζ−1)`-content
`2·(2e−1) = 37·(2m)` — the `p`-content clause `∃ m'', 2·(2e−1) = 37·(m''+1)` (with `m'' = 2m−1`,
`m ≥ 1`).

Proof: the genuine-unit anchor and the anchor-support `(z') = 𝔞₀ᵏ` (`¬𝔭 ∣ 𝔞₀`, so `¬𝔭 ∣ z'`) feed
the proven anchor-exponent identity `caseII_descended_content_eq` (`2e = 37m+1`, the sharp anchor
valuation `v_𝔭(x+y) = 37m+1` against `v_𝔭(λ) = 2`); the arithmetic `2·(2e−1) = 74m = 37·(2m)` and
`m ≥ 1` give the existential. -/
theorem caseII_pContentClause_of_genuineUnit_anchor
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {z' : 𝓞 (CyclotomicField 37 ℚ)} {u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    {ρ0 : CyclotomicField 37 ℚ} {e k : ℕ} (_hk : 1 ≤ k)
    (hanchor : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
            (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e * ρ0 ^ 37)
    (hz' : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) z' = ρ0 ^ 2)
    (hz'_span : Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k) :
    ∃ m'' : ℕ, 2 * (2 * e - 1) = 37 * (m'' + 1) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- `¬ (D.hζ − 1) ∣ z'` from the anchor-support `(z') = 𝔞₀ᵏ` (`𝔭 ∤ 𝔞₀`).
  have hz'_cop : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ z' := by
    have hnot : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [hz'_span]; intro hdvd
      exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz
        ((Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  -- The proven anchor-exponent / descended-content identity, then the existential.
  have hcontent := caseII_descended_content_eq D hp
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) hanchor hz' hz'_cop
  have hm : 1 ≤ m := D.toCaseIIData37.one_le_m
  exact ⟨2 * m - 1, by omega⟩

/-! ## 4. The genuine-integral-unit `ℓ ∣ z` extraction data, and the reduction to `p`-content -/

open scoped Classical in
/-- **[FLT37-CASEII-§9.1-DVDZ-GENUINE-UNIT-EXTRACTION-DATA] The §9.1 `ℓ ∣ ξ₁`-extraction data with
the genuine-integral-unit anchor** (a `def … : Prop`, **not** an axiom).

Identical to `CaseIISection91DvdZExtractionData37` (the §9.1 anchor equation, Assumption II, integer
witnesses, invariants, anchor-support, and the Lemma-9.6/9.7 `ℓ ∣ ξ₁` propagation), **strengthened**
so that the anchor unit `η₀` is a *genuine algebraic-integer unit* `η₀ = algebraMap u₀`
(`u₀ : (𝓞 K)ˣ`) — exactly the form Washington's `B₀`-principalization on `x+y` produces (the anchor
unit is the ratio of integers `(x+y)/(Λ^e·ρ₀³⁷)` whose ideal balances) — and with the ad-hoc
`p`-content existential clause **dropped** (it is *derivable* from the genuine-unit anchor, see
`caseIISection91PContentExtractionData37_of_dvdZGenuineUnit`). -/
def CaseIISection91DvdZGenuineUnitExtractionData37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) →
    ∀ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) →
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) →
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) →
      ∃ (e k : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (u : (CyclotomicField 37 ℚ)ˣ)
        (ρ0 : CyclotomicField 37 ℚ)
        (ω θ z' : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        1 ≤ e ∧ 1 ≤ k ∧
        -- anchor equation, **genuine-integral-unit** anchor `η₀ = algebraMap u₀`:
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
            (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
              ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e * ρ0 ^ 37 ∧
        (ηa : (CyclotomicField 37 ℚ)ˣ) = u ^ 37 * ηb ∧
        complexConj (CyclotomicField 37 ℚ)
            (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _)) =
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (u : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) z' = ρ0 ^ 2 ∧
        (∀ δ : (CyclotomicField 37 ℚ)ˣ,
          complexConj (CyclotomicField 37 ℚ) (δ : CyclotomicField 37 ℚ) =
              (δ : CyclotomicField 37 ℚ) →
          ((u : CyclotomicField 37 ℚ) ^ 2 *
                (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
              (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 =
            (δ : CyclotomicField 37 ℚ) *
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                  (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) *
              (ρ0 ^ 2) ^ 37 →
          (δ : CyclotomicField 37 ℚ) =
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (δ' : 𝓞 _)) ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ ∧
        ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ ∧
        ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 3 ∣ ω + θ ∧
        (∃ c : 𝓞 (CyclotomicField 37 ℚ),
          ω + θ * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 =
              ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) * c ∧
            ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣ c) ∧
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) =
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k ∧
        z' ∈ lv149 ∧ ω ∉ lv149 ∧ θ ∉ lv149

/-- **The genuine-integral-unit extraction data implies the `p`-content extraction data** (proven,
axiom-clean).

`CaseIISection91DvdZGenuineUnitExtractionData37 → CaseIISection91PContentExtractionData37`: the
genuine-integral-unit anchor `η₀ = algebraMap u₀` gives back the `Kˣ`-unit anchor (set `η₀` of the
`p`-content data to `(IsUnit.map (algebraMap …) u₀.isUnit).unit`), and — crucially — the dropped
`p`-content existential clause `∃ m'', 2·(2e−1) = 37·(m''+1)` is **derived** from the genuine-unit
anchor via `caseII_pContentClause_of_genuineUnit_anchor` (the proven anchor-exponent identity
`2e = 37m+1`).  Every other field maps across verbatim. -/
theorem caseIISection91PContentExtractionData37_of_dvdZGenuineUnit
    (h : CaseIISection91DvdZGenuineUnitExtractionData37) :
    CaseIISection91PContentExtractionData37 := by
  intro m D hcop ηa ηb ρa ρb hηa hηb hfa hfb
  obtain ⟨e, k, u0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
      hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span, hz'_mem, hω_notMem,
      hθ_notMem⟩ := h D hcop ηa ηb ρa ρb hηa hηb hfa hfb
  -- The `p`-content clause, derived from the genuine-integral-unit anchor.
  obtain ⟨m'', hpc⟩ := caseII_pContentClause_of_genuineUnit_anchor D.toRealCaseIIData37
    hk hanchor hz' hz'_span
  -- Repackage `η₀ = algebraMap u₀` as a `Kˣ`-unit for the `p`-content data's `η0` field.
  refine ⟨e, k, (IsUnit.map (algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ)).toMonoidHom u0.isUnit).unit, u, ρ0, ω, θ, z', δ',
    he, hk, ?_, hII, ?_, hω, hθ, hz', hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom',
    hz'_span, hz'_mem, hω_notMem, hθ_notMem, m'', hpc⟩
  · -- the anchor equation, with `η₀ = algebraMap u₀` written via the repackaged unit.
    rw [IsUnit.unit_spec]; exact hanchor
  · -- reality of the anchor unit `η₀ = algebraMap u₀`.
    rw [IsUnit.unit_spec]; exact hη0real

/-! ## 5. The cleanest FLT37 endpoint, on the genuine-integral-unit extraction data -/

/-- **Fermat's Last Theorem for `37`, via the genuine-integral-unit §9.1 `ℓ ∣ z` extraction data**
(proven, axiom-clean *given* the named inputs + carried Kellner) — the cleanest factor-count-frame
endpoint.

`FermatLastTheoremFor 37` from:
* `h_data` (`CaseIISection91DvdZGenuineUnitExtractionData37`): the §9.1 extraction data with the
  **genuine-integral-unit** anchor `η₀ = algebraMap u₀` (the form Washington's `B₀`-principalization
  produces; the ad-hoc `p`-content existential clause is **dropped** — it is *derived* here, via
  `caseIISection91PContentExtractionData37_of_dvdZGenuineUnit`);
* `h_cop`: the per-datum coprimality of the promoted Fermat variables (the universal is FALSE; kept
  threaded);
* `h_lemma96` (**Washington Lemma 9.6**, `ℓ ∤ xy`): the `ℓ ∣ ξ` domain non-emptiness;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried Kellner input.

Everything else is proven and supplied internally by
`fermatLastTheoremFor_thirtyseven_of_pContentDescent`:
Case I (Eichler), `¬ 37 ∣ h⁺` (Vandiver for 37), Case-II II1 (Washington Lemma 9.2), R3 (Washington
Lemma 9.9 regular indices), the proven §9.1 reassembly capstone, the proven anchor valuation
arithmetic, the proven well-founded factor-count descent **inside `p`-content** (so the
non-`p`-content gap never arises), and the proven `ℓ ∣ z` at the rational seed
(`furtwangler_37_149`).

Relative to `fermatLastTheoremFor_thirtyseven_of_pContentDescent`, this endpoint additionally
**discharges** the ad-hoc `p`-content clause (from the genuine-integral-unit anchor) and banks the
proven single-index expansion + instance-wise Assumption II (`Cor815SingleIndexExpansion37` proven,
`caseII_descentUnit_isPow_of_dvdZ_instance` proven), leaving the §9.1 **construction** itself
(`h_data`) as the sole genuine R2 residual alongside the threaded `h_cop`/`h_lemma96` and carried
Kellner. -/
theorem fermatLastTheoremFor_thirtyseven_of_section91GenuineUnitExtraction
    (h_data : CaseIISection91DvdZGenuineUnitExtractionData37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_pContentDescent
    (caseIISection91PContentExtractionData37_of_dvdZGenuineUnit h_data)
    h_cop h_lemma96 noSecondOrderIrregular

/-! ## 6. Non-vacuity of the genuine-integral-unit extraction data (a genuine implication) -/

/-- **Non-vacuity of `CaseIISection91DvdZGenuineUnitExtractionData37` (antecedent inhabited).**

For a combined `ℓ ∣ z` real datum `D` with coprime Fermat variables, the factor-equation outputs the
extraction data is keyed to **exist** (`caseII_section91_factorEquations_etaOne_etaTwo`, from the
proven product half).  So the genuine-integral-unit residual consumes inhabited input — it is a
genuine implication, not vacuously true for the wrong reason.  (Identical antecedent to the
`p`-content data; the strengthening is purely in the *conclusion*: the anchor unit is integral and
the `p`-content clause is dropped because it is derivable.) -/
theorem caseIISection91DvdZGenuineUnitExtractionData37_antecedent_inhabited
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ),
      complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
          (ηa : CyclotomicField 37 ℚ) ∧
      complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
          (ηb : CyclotomicField 37 ℚ) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) :=
  caseIISection91PContentExtractionData37_antecedent_inhabited D hcop

end BernoulliRegular.FLT37.Eichler

end

end

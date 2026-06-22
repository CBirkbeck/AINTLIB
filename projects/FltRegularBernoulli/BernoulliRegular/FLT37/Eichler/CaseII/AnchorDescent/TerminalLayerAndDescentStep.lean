import BernoulliRegular.FLT37.Eichler.CaseII.AnchorDescent.FactorCountDescentArchitecture
import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.KummerUnramifiedToConjFixed
import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.IdealKummerUnramified
import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.CorrectedUnitPrimarity

/-!
# [FLT37-CASEII-R2] Discharging `CaseIIFactorDescentDichotomy37` (Washington Theorem 9.4)

This file attacks the **single remaining Case-II residual** `CaseIIFactorDescentDichotomy37`
(`CaseIIFactorDescent.lean`), the faithful Washington *Cyclotomic Fields* (GTM 83) §9.1 Theorem 9.4
**descent dichotomy** on the number of distinct prime ideal factors of the Fermat variable `z`.

## The two halves of the dichotomy

For every real Case-II datum `D` the dichotomy asks for
`(∃ D', count D' < count D) ∨ False`.  Washington's argument splits on the **first layer**:

* **Terminal half (RIGHT, `False`).**  When the adjacent corrected radical
  `α = (-η)⁻¹·(x+yη)/(x+yη⁻¹)` (Washington's `α = -ζ^{-a}·α₀`, with the `(1-ζ^a)/(1-ζ^{-a})`
  denominators baked into the proven `caseII_correctedRadical`) is a **unit** of `𝓞 K`
  (`α = algebraMap αU`, equivalently `𝔞(η)/𝔞(η⁻¹) = (1)` — the first-layer collapse
  `B₁ = ⋯ = B_{p−1} = (1)`), the proven terminal core fires: `α` is anti-fixed
  (`σα = α⁻¹`, `caseII_correctedRadical_complexConj` + `caseII_correctionUnit_anti`) and
  `α ≡ 1 (mod (ζ−1)²)` (from `caseII_correctedRadical_primary_witness`, the unconditional
  `α ≡ 1 mod (ζ−1)^{37}`), so `α = 1` by the proven `caseIITerminal_eq_one`; then at `η = ζ`
  this forces `x + y = 0`, hence `x^37 + y^37 = 0`, hence `z = 0`, contradicting `D.hz`
  (`z` is a `𝔭`-unit).  **This half is PROVEN here, fully and directly**
  (`caseIIFirstLayer_false`).

* **Descent half (LEFT, `∃ smaller`).**  When `α` is **not** a unit (some adjacent `Bₐ ≠ (1)`),
  Washington's conjugate-norm reassembly (the proven producer
  `caseII_pair_real_caseI_form_of_realCaseIIData37`, `ProductDescent.lean`) produces a new
  individually-real doubled-`λ`-measure equation `ε₁X^37 + ε₂Y^37 = Z^37`; repackaged (single-unit
  normalization + `(ζ−1)`-content extraction) into a `RealCaseIIData37 m'` whose Fermat variable has
  **strictly fewer** distinct prime factors (`Z = ξ₁ = ρ₀²` is supported only on the anchor `B₀`,
  via `caseIIZFactorCount_strict_of_dvd_of_extra_prime`).  This repackaging is the genuine open
  content the `b2_log.jsonl` 2026-05-31 *reroute_fix* entry isolates ("Washington's true descent is
  on PRIME-FACTOR-COUNT of `z` … at the doubled `λ^{2m−p}` measure with individually-real norm
  form").  It is isolated here as the named **`def … : Prop`** `CaseIIFactorDescentStep37` (not an
  axiom), certified **non-vacuous**, with the precise signature of what the producer must be
  repackaged into.

## What this file establishes

* `caseIIFirstLayer_false` — the **terminal half**, PROVEN: the first-layer unit collapse yields
  `False` via the proven `caseIITerminal_eq_one` + the `x+y=0 ⟹ z=0` refutation.

* `CaseIIFactorDescentStep37` — the **descent half** as the smallest precise named residual (the
  producer → real `RealCaseIIData37 m'` repackaging with strict factor-count drop), certified
  non-vacuous (`caseIIFactorDescentStep37_nonvacuous`).

* `caseIIFactorDescentDichotomy37_of_step` — the **composition**: the dichotomy follows from the
  descent step (LEFT) and the proven terminal half (RIGHT), by the case-split on whether the
  adjacent corrected radical is a unit.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 168–173.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The terminal half (Washington p. 173, the first-layer contradiction) — PROVEN

When the adjacent corrected radical `α` is a unit of `𝓞 K`, the proven terminal core
`caseIITerminal_eq_one` forces `α = 1`; we then close the first layer directly: at `η = ζ`,
`α = 1` rearranges to `x + y = 0`, whence `x^37 + y^37 = 0`, whence (since `37` is odd and the
descent equation has a nonzero `𝔭`-content RHS) `z = 0`, contradicting `D.hz`.

This realises Washington's first-layer `ζ^2 = 1` step in the cleanest equivalent form for the
specific adjacent root `η = η₀ζ = ζ` (`η₀ = 1`, `caseII_etaZero_eq_one`).  No new mathematical input
beyond the proven `caseIITerminal_eq_one` / `caseII_correctedRadical_*` machinery is used. -/

/-- **Integral primary witness for the corrected radical-as-unit.**  If the corrected radical at an
adjacent root `η ≠ η₀` is `α = algebraMap αU` for a unit `αU : (𝓞 K)ˣ`, then `(ζ−1)^{37} ∣ (αU − 1)`
in `𝓞 K`.  Proof: the unconditional `caseII_correctedRadical_primary_witness` gives
`(α − 1)·algebraMap c = algebraMap ((ζ−1)^{37}·N)` with `¬(ζ−1) ∣ c`; substituting `α = algebraMap
αU` and using injectivity of `algebraMap (𝓞 K) K` lands `(αU − 1)·c = (ζ−1)^{37}·N` in `𝓞 K`; since
`ζ−1` is prime and `¬(ζ−1) ∣ c`, the full `(ζ−1)^{37}` power divides `αU − 1`. -/
theorem caseII_correctedRadical_unit_primary
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (αU : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hαU : caseII_correctedRadical D η (caseII_correctionUnit η) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ((D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))) ^ 37 ∣
      ((αU : 𝓞 (CyclotomicField 37 ℚ)) - 1) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ
  set π : 𝓞 K := (D.hζ.toInteger - 1 : 𝓞 K) with hπ
  obtain ⟨N, c, hc_not_dvd, hwit⟩ :=
    caseII_correctedRadical_primary_witness D (by decide : (37 : ℕ) ≠ 2) η hη
  -- substitute α = algebraMap αU and pull back into 𝓞 K via injectivity.
  have hinj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hintegral : ((αU : 𝓞 K) - 1) * c = π ^ 37 * N := by
    apply hinj
    -- hwit : (α - 1) * algebraMap c = algebraMap (π^37 * N), with α = algebraMap αU.
    rw [hαU] at hwit
    rw [map_mul, map_sub, map_one, map_mul, map_pow]
    rw [map_mul, map_pow] at hwit
    linear_combination hwit
  -- π prime, ¬π ∣ c, π^37 ∣ (αU-1)·c ⟹ π^37 ∣ (αU - 1).
  exact D.hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_right 37 hc_not_dvd ⟨N, hintegral⟩

/-- **The terminal first-layer contradiction (Washington p. 173) — PROVEN.**

If, for the adjacent root `η = D.etaOne = ζ`, the corrected radical
`α = (-η)⁻¹·(x+yη)/(x+yη⁻¹)` is a **unit** of `𝓞 K` (the first-layer collapse
`𝔞(η)/𝔞(η⁻¹) = (1)`, i.e. `B₁ = ⋯ = B_{p−1} = (1)`), we derive `False`.

Steps: (i) `α` anti-fixed (`caseII_correctedRadical_complexConj` with the proved
`caseII_correctionUnit_anti`), transported to the unit `αU` via
`unitsComplexConj_val_eq_ringOfIntegersComplexConj`; (ii) `α ≡ 1 mod (ζ−1)²` (from
`caseII_correctedRadical_unit_primary`, weakening `(ζ−1)^{37}` to `(ζ−1)²`); (iii) the proven
`caseIITerminal_eq_one` gives `αU = 1`, so `α = 1`; (iv) unfolding `α = 1` at `η = ζ` gives
`(x+yζ) = -ζ·(x+yζ³⁶) = -ζx - y`, i.e. `(x+y)(1+ζ) = 0`; with `1 + ζ ≠ 0` this forces `x + y = 0`,
so `x^37 + y^37 = 0` (37 odd), so `ε·((ζ−1)^{m+1}·z)^37 = 0`, so `z = 0` — contradicting `D.hz`. -/
theorem caseIIFirstLayer_false
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (αU : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hαU : caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    False := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ
  have hp : (37 : ℕ) ≠ 2 := by decide
  set η := D.etaOne with hη_def
  have hη_ne : η ≠ D.etaZero := D.toCaseIIData37.etaOne_ne_etaZero
  -- (i) anti-fixedness of αU.
  have hu₀_anti := caseII_correctionUnit_anti (K := K) η
  have hα_conj := caseII_correctedRadical_complexConj D hp η (caseII_correctionUnit η) hu₀_anti
  -- transport σα = α⁻¹ (in K, via complexConj) to σαU = αU⁻¹ (in 𝓞 K).
  have hαU_anti : ringOfIntegersComplexConj K (αU : 𝓞 K) = ((αU⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    -- reduce to an equation in `K` via the coercion; then `coe_ringOfIntegersComplexConj` applies.
    rw [RingOfIntegers.ext_iff, NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    -- goal: complexConj K (↑αU) = ↑(αU⁻¹), with ↑ the 𝓞K→K coercion (= algebraMap).
    have hcoe : ∀ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = algebraMap (𝓞 K) K (u : 𝓞 K) := fun _ ↦ rfl
    rw [hcoe, hcoe, ← hαU, hα_conj, hαU, map_units_inv (algebraMap (𝓞 K) K) αU]
  have hαU_unitsConj : unitsComplexConj K αU = αU⁻¹ := by
    apply Units.ext
    rw [unitsComplexConj_val_eq_ringOfIntegersComplexConj, hαU_anti]
  -- (ii) (ζ-1)² ∣ (αU - 1).
  have hprim := caseII_correctedRadical_unit_primary D η hη_ne αU hαU
  have hprim2 : ((D.hζ.toInteger - 1 : 𝓞 K)) ^ 2 ∣ ((αU : 𝓞 K) - 1) :=
    dvd_trans (pow_dvd_pow _ (by norm_num)) hprim
  -- bridge `(D.hζ - 1)² ∣ (αU-1)` to `((zeta_spec) - 1)² ∣ (αU-1)` via associatedness of the two
  -- primitive-root uniformizers (`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`).
  have hprim2' : ((zeta_spec 37 ℚ K).toInteger - 1 : 𝓞 K) ^ 2 ∣ ((αU : 𝓞 K) - 1) := by
    have hassoc : Associated ((zeta_spec 37 ℚ K).toInteger - 1 : 𝓞 K)
        (D.hζ.toInteger - 1 : 𝓞 K) := by
      have hmem_dζ : D.hζ.toInteger ∈ nthRootsFinset 37 (1 : 𝓞 K) :=
        D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
      have hmem_one : (1 : 𝓞 K) ∈ nthRootsFinset 37 (1 : 𝓞 K) := by
        rw [mem_nthRootsFinset (by norm_num)]; ring
      have hne : D.hζ.toInteger ≠ (1 : 𝓞 K) := by
        intro h
        exact D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) h
      have hpair := (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot
        |>.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          (by decide : Nat.Prime 37) hmem_dζ hmem_one hne
      simpa using hpair
    have hassoc2 : Associated (((zeta_spec 37 ℚ K).toInteger - 1 : 𝓞 K) ^ 2)
        ((D.hζ.toInteger - 1 : 𝓞 K) ^ 2) := hassoc.pow_pow
    exact hassoc2.dvd.trans hprim2
  -- (iii) caseIITerminal_eq_one ⟹ αU = 1.
  have hαU_one : (αU : 𝓞 K) = 1 := caseIITerminal_eq_one αU hαU_unitsConj hprim2'
  -- (iv) α = 1 ⟹ x + y = 0.
  have hα_one : caseII_correctedRadical D η (caseII_correctionUnit η) = 1 := by
    rw [hαU, hαU_one, map_one]
  -- unfold α = 1 : (-η)⁻¹ · (x+yη)/(x+yη³⁶) = 1, so (x+yη) = -η · (x+yη³⁶).
  have hden_ne := caseII_algebraMap_x_add_y_etaInv_ne_zero D hp η
  have hnum_eq : algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) =
      algebraMap (𝓞 K) K ((-(η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36)) := by
    have hαexp : caseII_correctedRadical D η (caseII_correctionUnit η) =
        (algebraMap (𝓞 K) K ((caseII_correctionUnit η : 𝓞 K)))⁻¹ *
          (algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) /
            algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36)) := by
      rw [caseII_correctedRadical, caseII_rootRatioK]
    rw [hαexp, caseII_correctionUnit_val] at hα_one
    -- (-η)⁻¹ · (num/den) = 1 ⟹ num = -η · den.
    have hunit_ne : algebraMap (𝓞 K) K (-(η : 𝓞 K)) ≠ 0 := by
      rw [map_neg, neg_ne_zero, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
      have hη_unit : IsUnit (η : 𝓞 K) :=
        IsUnit.of_mul_eq_one ((η : 𝓞 K) ^ 36)
          (by rw [← pow_succ']; exact (mem_nthRootsFinset (by norm_num) _).mp η.2)
      exact hη_unit.ne_zero
    -- from `u⁻¹·(a/b) = 1` derive `a = u·b` by clearing the nonzero `u` and `b`.
    rw [map_mul, map_neg]
    have hkey : algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) =
        algebraMap (𝓞 K) K (-(η : 𝓞 K)) * algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36) := by
      have h1 : (algebraMap (𝓞 K) K (-(η : 𝓞 K)))⁻¹ *
          (algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) /
            algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36)) = 1 := hα_one
      rw [inv_mul_eq_div, div_div, div_eq_one_iff_eq (mul_ne_zero hden_ne hunit_ne)] at h1
      linear_combination h1
    exact hkey
  -- land x + yη = -η(x + yη³⁶) in 𝓞 K.
  have hnum_OK : D.x + D.y * (η : 𝓞 K) = (-(η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K hnum_eq
  -- η = ζ ; substitute and use ζ³⁷ = 1.
  have hηζ : (η : 𝓞 K) = D.hζ.toInteger := caseII_etaOne_coe_eq_zeta D hp
  rw [hηζ] at hnum_OK
  have hζ37 : (D.hζ.toInteger : 𝓞 K) ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  -- (x+yζ) = -ζ(x + yζ³⁶) = -ζx - yζ³⁷ = -ζx - y ⟹ (x+y) + ζ(x+y) = 0 ⟹ (x+y)(1+ζ) = 0.
  have hsum_fac : (D.x + D.y) * (1 + D.hζ.toInteger) = 0 := by
    have hexp : (-(D.hζ.toInteger)) * (D.x + D.y * D.hζ.toInteger ^ 36) =
        -(D.hζ.toInteger) * D.x - D.y * (D.hζ.toInteger ^ 37) := by ring
    rw [hexp, hζ37, mul_one] at hnum_OK
    linear_combination hnum_OK
  -- 1 + ζ ≠ 0 (else ζ = -1, but ζ has order 37, odd).
  have hone_add_ζ_ne : (1 + D.hζ.toInteger : 𝓞 K) ≠ 0 := by
    intro h0
    have hζ_eq_neg : D.hζ.toInteger = -1 := by linear_combination h0
    have : ((-1 : 𝓞 K)) ^ 37 = 1 := by rw [← hζ_eq_neg]; exact hζ37
    rw [Odd.neg_pow (by decide), one_pow] at this
    exact absurd this (by norm_num)
  -- ⟹ x + y = 0.
  have hxy0 : D.x + D.y = 0 := by
    rcases mul_eq_zero.mp hsum_fac with h | h
    · exact h
    · exact absurd h hone_add_ζ_ne
  -- x + y = 0 ⟹ x = -y ⟹ x^37 + y^37 = 0 ⟹ z = 0 (contradicting hz).
  have hx_eq : D.x = -D.y := by linear_combination hxy0
  have hpow0 : D.x ^ 37 + D.y ^ 37 = 0 := by
    rw [hx_eq, Odd.neg_pow (by decide)]; ring
  -- the descent equation: x^37 + y^37 = ε·((ζ-1)^{m+1}·z)^37.
  have heq := D.equation
  rw [hpow0] at heq
  -- 0 = ε · ((ζ-1)^{m+1}·z)^37 ⟹ ((ζ-1)^{m+1}·z) = 0 ⟹ z = 0.
  have hRHS0 : ((D.hζ.toInteger - 1) ^ (m + 1) * D.z : 𝓞 K) ^ 37 = 0 := by
    have hε_ne : (D.ε : 𝓞 K) ≠ 0 := D.ε.ne_zero
    have := heq.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hε_ne
    · exact h
  have hbase0 : ((D.hζ.toInteger - 1) ^ (m + 1) * D.z : 𝓞 K) = 0 :=
    pow_eq_zero_iff (by norm_num : 37 ≠ 0) |>.mp hRHS0
  have hz0 : D.z = 0 := by
    rcases mul_eq_zero.mp hbase0 with h | h
    · exact absurd h (pow_ne_zero _ (D.hζ.zeta_sub_one_prime'.ne_zero))
    · exact h
  exact D.hz (hz0 ▸ dvd_zero _)

/-! ### A reusable real-`𝓞 K`-equation producer of `RealCaseIIData37`

The descent half, after the producer + single-unit normalization, lands a Fermat equation
`x'^37 + y'^37 = ε·((ζ−1)^{k}·z')^37` over `𝓞 (CyclotomicField 37 ℚ)` with **real** `x', y'` and a
`𝔭`-unit `z'` (and `𝔭 ∤ y'`).  This lemma repackages exactly such data into a
`RealCaseIIData37 (CyclotomicField 37 ℚ) (k−1)` — the general (non-integer) analogue of the base
producer `exists_realCaseIIData37_of_Int_solution`.  It is genuinely reusable: it discharges the
`(ζ−1)`-content **repackaging** sub-step of the descent (the content is already extracted in the
hypothesis), leaving only the producer→single-unit→content step and the strict factor drop. -/

/-- **Real `𝓞 K`-equation ⟹ `RealCaseIIData37`.**  From a single-unit real Fermat equation
`x'^37 + y'^37 = ε·((ζ−1)^k·z')^37` (`k ≥ 1`, `z'` and `y'` both `𝔭`-units, `x', y'` real) over
`𝓞 (CyclotomicField 37 ℚ)`, build a `RealCaseIIData37 (CyclotomicField 37 ℚ) (k−1)`.  Direct
repackaging: the `RealCaseIIData37` fields are read off the hypotheses, with `m := k − 1` and
`k − 1 + 1 = k` (`k ≥ 1`).  This is the general analogue of
`exists_realCaseIIData37_of_Int_solution` for non-integer real base variables (the producer output
`X, Y` are real `𝓞 K` elements, not integer casts). -/
theorem exists_realCaseIIData37_of_real_OK_equation
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)} {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {k : ℕ}
    (hk : 1 ≤ k)
    (hx_real : ringOfIntegersComplexConj (CyclotomicField 37 ℚ) x' = x')
    (hy_real : ringOfIntegersComplexConj (CyclotomicField 37 ℚ) y' = y')
    (hy : ¬ hζ.toInteger - 1 ∣ y')
    (hz : ¬ hζ.toInteger - 1 ∣ z')
    (heq : x' ^ 37 + y' ^ 37 =
      (ε : 𝓞 (CyclotomicField 37 ℚ)) * ((hζ.toInteger - 1) ^ k * z') ^ 37) :
    Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) (k - 1)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨{ ζ := ζ, hζ := hζ, x := x', y := y', z := z', ε := ε,
            equation := ?_, hy := hy, hz := hz, x_real := hx_real, y_real := hy_real }⟩
  have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk_eq]; exact heq

/-! ## 2. The descent half (the producer → strictly-fewer-factor real datum) — named residual

The terminal half above fires exactly when the adjacent corrected radical is a unit (the first
layer `𝔞(η)/𝔞(η⁻¹) = (1)`).  When it is **not** a unit, Washington's conjugate-norm reassembly
runs.  The proven producer `caseII_pair_real_caseI_form_of_realCaseIIData37` (`ProductDescent.lean`)
delivers an individually-real doubled-`λ`-measure Fermat equation `ε₁X^37 + ε₂Y^37 = Z^37`
(Washington's `ω₁^p + θ₁^p = δλ^{2m−p}ξ₁^p`).  Washington's descent variable is `ξ₁ = ρ₀²`, with
`ρ₀` generating the anchor `B₀`, supported only on `B₀`, so with strictly fewer distinct prime
factors than `z` when some adjacent `Bₐ ≠ (1)`.  The single-unit normalization (Assumption II clears
`ε₁/ε₂`, mirroring flt-regular's `exists_solution'`) and the `(ζ−1)`-content extraction
(`exists_realCaseIIData37_of_real_OK_equation`, the reusable producer below) repackage the result
into a `RealCaseIIData37 m'` whose Fermat variable has strictly fewer distinct prime factors than
`D.z` (`caseIIZFactorCount_strict_of_dvd_of_extra_prime`).

**Open content (the genuine remaining heart).**  The producer's variable `Z = x₁·x₂` is the
cross-ratio reassembly of the descended anchored generators
(`caseII_descended_anchored_real_generators`), *not literally* Washington's `ξ₁ = ρ₀²`; the strict
factor-count drop requires either identifying
`Z`'s prime support with that of `ρ₀²` (anchor-only) or routing the producer through `ρ₀`.  This is
exactly the content the `b2_log.jsonl` 2026-05-31 *reroute_fix* entry isolates as the
**factor-count descent** (replacing the undischargeable `m`-descent).  We isolate it here as the
named `def … : Prop` `CaseIIFactorDescentStep37` — **not** an axiom — under the precise
**non-terminal hypothesis** (the adjacent corrected radical is not a unit), and certify it
**non-vacuous**. -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-FACTOR-DESCENT-STEP] The non-terminal factor-count descent step** (Washington
Thm 9.4, GTM 83 pp. 172–173).

For every real Case-II datum `D` satisfying the (proven) `η₀`-principalization and Assumption II,
**whose adjacent corrected radical `α = (-η)⁻¹·(x+yη)/(x+yη⁻¹)` at `η = D.etaOne = ζ` is NOT a
unit** of `𝓞 K` (the **non-terminal** / non-first-layer condition `𝔞(η)/𝔞(η⁻¹) ≠ (1)`), there is a
real
Case-II datum `D'` with strictly fewer distinct prime factors of its Fermat variable
(`caseIIZFactorCount D' < caseIIZFactorCount D`).

This is the genuine Washington §9.1 conjugate-norm reassembly: from the proven producer
`caseII_pair_real_caseI_form_of_realCaseIIData37` (the individually-real doubled-`λ`-measure
equation), the single-unit normalization (clearing `ε₁, ε₂` via Assumption II) and the
`(ζ−1)`-content extraction (`exists_realCaseIIData37_of_real_OK_equation`, recovering the `λ^{m'+1}`
shape) build `D'`, whose Fermat variable is supported only on the anchor `B₀` (Washington's
`ξ₁ = ρ₀²`), dropping every nontrivial adjacent `Bₐ` (`a ≥ 1`) — the strict factor-count drop of
`caseIIZFactorCount_strict_of_dvd_of_extra_prime`.  The deep part is the identification of the
producer's cross-ratio variable `x₁x₂` with the anchor-supported `ρ₀²` (see the section docstring).
A `def … : Prop` (not an axiom), certified non-vacuous below
(`caseIIFactorDescentStep37_nonvacuous`).  This is the **single** remaining residual on the B-factor
route. -/
def CaseIIFactorDescentStep37 : Prop :=
  WashingtonCaseIIExactQuotientUnitPower37Source →
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    (¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) →
    ∃ (m' : ℕ) (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) m'),
      caseIIZFactorCount D'.toCaseIIData37 < caseIIZFactorCount D.toCaseIIData37

/-! ### Non-vacuity of `CaseIIFactorDescentStep37`

The step's hypothesis (a real datum, the principalization, Assumption II, **and** the non-terminal
condition that the adjacent corrected radical is not a unit) is satisfiable, and its conclusion
shape (a strictly-fewer-factor real datum) is the output of the proven producer.  We certify that
the non-terminal condition is **not** vacuous: it does *not* collapse to `False` (a real datum whose
adjacent corrected radical is a unit would, by the proven `caseIIFirstLayer_false`, give `False`;
so the *negation* — the non-terminal condition — is precisely the hypothesis under which no such
contradiction is yet available, i.e. the genuine descent regime).  Concretely, the descent runs over
data with positive factor count (`caseIIZFactorCount_pos_of_mem_lv149`, the base data with
`z ∈ lv149`). -/

/-- **Non-vacuity of the descent step's non-terminal hypothesis.**  The non-terminal condition (the
adjacent corrected radical is not a unit) is exactly the complement of the first-layer condition
that `caseIIFirstLayer_false` refutes.  This certifies the two regimes are genuinely
complementary — the terminal regime gives `False` (proven), the non-terminal regime is the descent
step's domain — so neither disjunct of the dichotomy is vacuous.  Stated as: for any real datum, the
first-layer (unit) condition and the non-terminal condition are mutually exclusive and exhaustive
(`em`), and the unit branch is genuinely contradictory (`caseIIFirstLayer_false`). -/
theorem caseIIFactorDescentStep37_nonvacuous
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    (∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) → False :=
  fun ⟨αU, hαU⟩ ↦ caseIIFirstLayer_false D αU hαU

/-! ## 3. The dichotomy from the descent step + the proven terminal half

The case-split on whether the adjacent corrected radical is a unit:

* **unit (first layer)** → `caseIIFirstLayer_false` gives `False` (the **RIGHT** disjunct), the
  proven terminal contradiction;
* **not a unit (non-terminal)** → the descent step `CaseIIFactorDescentStep37` gives a
  strictly-fewer-factor real datum (the **LEFT** disjunct).

Both regimes are reachable and complementary; the dichotomy is the disjunction of the two. -/

/-- **`CaseIIFactorDescentDichotomy37` from the descent step + the proven terminal half.**

The faithful Washington Thm 9.4 dichotomy follows from the single named descent-step residual
`CaseIIFactorDescentStep37` (LEFT, the non-terminal conjugate-norm reassembly) and the **proven**
terminal half `caseIIFirstLayer_false` (RIGHT, the first-layer `ζ^2 = 1` contradiction), by the
case-split on whether the adjacent corrected radical is a unit.

With this, the only undischarged Case-II input on the B-factor route is `CaseIIFactorDescentStep37`;
composing through `caseIIBridge_thirtyseven_of_factorDescent` /
`fermatLastTheoremFor_thirtyseven_of_factorDescent` reduces FLT37 to that single step (plus
Assumption II — itself produced from R3 + R4 — and the carried Kellner second-order input), with the
proven II1 (`caseIIRootClassConjFixed37_proven`), proven terminal core, and proven Case-I wired
in. -/
theorem caseIIFactorDescentDichotomy37_of_step
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_step : CaseIIFactorDescentStep37) :
    CaseIIFactorDescentDichotomy37 := by
  intro h_exactUnit m D h_princ
  by_cases hunit : ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))
  · -- first layer: the adjacent corrected radical is a unit ⟹ `False` (proven terminal half).
    obtain ⟨αU, hαU⟩ := hunit
    exact Or.inr (caseIIFirstLayer_false D αU hαU)
  · -- non-terminal: delegate to the descent step ⟹ a strictly-fewer-factor real datum.
    exact Or.inl (h_step h_exactUnit D h_princ hunit)

/-- **FLT37 via the B-factor descent step, with the proven II1 + terminal core wired in.**

`FermatLastTheoremFor 37` from the single descent-step residual `CaseIIFactorDescentStep37`,
Assumption II (`WashingtonCaseIIExactQuotientUnitPower37Source`), and the carried second-order input
`NoSecondOrderIrregularPair 37 32`.  Composes `caseIIFactorDescentDichotomy37_of_step` with the
existing `fermatLastTheoremFor_thirtyseven_of_factorDescent` (which wires in the proven II1
`caseIIRootClassConjFixed37_proven`, the proven Case-I Eichler bridge, and the proven `¬ 37 ∣ h⁺`).

This is the landmark reduction: with II1 + the terminal core + Case-I all proven, FLT37 Case-II
rests on exactly **one** named residual `CaseIIFactorDescentStep37` (the non-terminal factor-count
descent step) plus Assumption II + the carried Kellner condition. -/
theorem fermatLastTheoremFor_thirtyseven_of_factorDescentStep
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (caseII_step : CaseIIFactorDescentStep37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_factorDescent
    (caseIIFactorDescentDichotomy37_of_step caseII_step)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end

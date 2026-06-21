import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonCaseIIClean

/-!
# [F2] The aux-prime `ℓ`-propagation conjuncts of the clean Case-II residual, PROVEN

This file discharges the **aux-prime Lemma-9.6/9.7 `ℓ`-propagation conjuncts** of the clean
Case-II residual `CaseIIWashingtonCaseII37` (`CaseIIWashingtonCaseIIClean.lean`): for a real
`ℓ ∣ z` datum `D : RealCaseIIDvdZData37 m` (datum fields `z ∈ 𝔩`, `x ∉ 𝔩`, `y ∉ 𝔩`,
`𝔩 = lv149`), the proven L2 factor equations at `ζ, ζ²`, and the proven L1 anchor equation:

* **(a)** `ρ₀² ∈ 𝔩` (`caseII_dvdZ_rho0_sq_mem_lv149`) — Washington p. 178: "If we can prove that
  `l ∣ (ω + θ)`, then every prime divisor of `l` divides `ρ₀`".  From the **proven** Lemma 9.8
  `x + y ∈ 𝔩` (`caseII_real_x_add_y_mem_of_dvd_z`), the anchor pulled back to `𝓞 K`
  (`x + y = u₀·Λ^e·ρ₀³⁷`, `Λ = (1−ζ)(1−ζ³⁶)`), primality of `𝔩`, `𝔩` unramified
  (`1 − ζ^k ∉ 𝔩`), and `u₀ ∉ 𝔩` (unit), the prime `𝔩` must divide `ρ₀³⁷`, hence `ρ₀`, hence
  `ρ₀²`.

* **(b)** every integer witness `ω` of `v²·ρ_a·σρ_a` has `ω ∉ 𝔩`
  (`caseII_dvdZ_omega_witness_notMem_lv149`) — if `ω ∈ 𝔩` then (`𝔩` prime, `v` an integral
  unit) one of the integral factor generators `r_a, σr_a` lies in `𝔩`, so the factor equation
  (or its `σ`-transport `x + ζ³⁶y = (1−ζ³⁶)·σu_a·(σr_a)³⁷`) puts `x + ζ^{±1}·y ∈ 𝔩`;
  subtracting the proven `x + y ∈ 𝔩` gives `(ζ^{±1} − 1)·y ∈ 𝔩` with `ζ^{±1} − 1 ∉ 𝔩`
  (`ℓ` unramified) and `y ∉ 𝔩` (Lemma 9.6, datum field) — contradiction.

* **(c)** every integer witness `θ` of `−ρ_b·σρ_b` has `θ ∉ 𝔩`
  (`caseII_dvdZ_theta_witness_notMem_lv149`) — identical with `r_b` at `ζ²` (factors
  `x + ζ^{±2}·y`).

The triple is packaged in the residual's exact conjunct shapes by
`caseII_dvdZ_ellPropagation_withUnits`, and `caseII_dvdZ_caseII_conclusion_of_realAssumptionII`
produces the **full `∃ v`-conclusion** of `CaseIIWashingtonCaseII37` from a real Assumption-II
witness (`v` real, `η_a = v³⁷·η_b`) — so the residual's conclusion is reduced to real
Assumption II alone, given the integral-unit witnesses.

## Soundness boundary (why the integral-unit witnesses `u_a, u_b` are required)

Conjuncts (b)/(c) are proven **with the integral-unit witnesses** `u_a, u_b : (𝓞 K)ˣ`
(`algebraMap u_a = η_a`, `algebraMap u_b = η_b`) — exactly what the strengthened producer
`caseII_section91_factorEquations_etaOne_etaTwo_withUnits` supplies where the residual is
consumed (`caseIISection91PContentExtractionDataWithUnits37_of_caseII`).  Over the *bare* field
antecedent of `CaseIIWashingtonCaseII37` (field units `η_a, η_b : Kˣ` with only reality + the
factor equations) the conditional conjuncts are **not derivable**: the antecedent is invariant
under the real rescaling `η_b ↦ η_b·149^{∓37}`, `ρ_b ↦ 149^{±1}·ρ_b` (`149` is real and the
factor equation constrains only `η_b·ρ_b³⁷`), and under `η_b ↦ η_b·149^{−37}`, `ρ_b ↦ 149·ρ_b`
any integral witness `θ₀` of `−ρ_bσρ_b` is replaced by the witness `149²·θ₀ ∈ 𝔩` of the
rescaled block — flipping conjunct (c) from true to false while every hypothesis of the
antecedent (reality of `149`, the factor equation, the datum, coprimality, the anchor) is
preserved.  The integral-unit witnesses pin the `𝔩`-adic normalisation (`v_𝔩(η_b) = 0`), and
the same applies to the Assumption-II unit `v` in conjunct (b) (here `v` is integral via
`caseII_assumptionII_unit_integral` from `η_a = v³⁷·η_b` and `u_a, u_b`).  Conjunct (a) needs
no unit witnesses: `ρ₀` is integral by the anchor's shape.

## The deep input

The only deep ingredient is Washington **Lemma 9.8** (`ℓ ∣ ω + θ`, i.e. `x + y ∈ 𝔩`), which is
**proven** over real `ℓ ∣ z` data (`caseII_real_x_add_y_mem_of_dvd_z`,
`CaseIILemma98RealData.lean`) from the datum fields (`z ∈ 𝔩`, `x, y ∉ 𝔩` — Lemmas 9.6/9.7) and
the carried Kellner input `hSO : NoSecondOrderIrregularPair 37 32` (which the FLT37 endpoint
`fermatLastTheoremFor_thirtyseven_of_washington_caseII` already carries).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.3, pp. 176–180
  (Theorem 9.5, Lemmas 9.6–9.8; the `ℓ`-propagation transition on p. 178).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. `ℓ = 149` is unramified: no nontrivial `37`-th root of unity is `≡ 1 (mod 𝔩)`

The generic form of `caseII_zeta_sub_one_notMem_lv149`, for an **arbitrary** nontrivial `37`-th
root of unity `w ∈ 𝓞 K` (not just a designated primitive root): the conjugates `ζ^k` of a
datum's primitive root and the anchor's `zeta_spec`-powers are all covered uniformly. -/

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **`w − 1 ∉ lv149` for any `37`-th root of unity `w ≠ 1`** (proven, axiom-clean).

If `w − 1 ∈ lv149`, then in `𝓞 K / 𝔩` every `w^i ≡ 1`, so the vanishing geometric sum
`∑_{i<37} w^i = 0` (valid since `w ≠ 1` in a domain: `(∑ w^i)(w−1) = w³⁷ − 1 = 0`) reduces to
`37 ≡ 0 (mod 𝔩)`, contradicting `caseII_thirtyseven_notMem_lv149` (`𝔩` lies over `149`). -/
theorem caseII_root_of_unity_sub_one_notMem_lv149
    {w : 𝓞 (CyclotomicField 37 ℚ)} (hw37 : w ^ 37 = 1) (hw1 : w ≠ 1) :
    w - 1 ∉ lv149 := by
  intro hmem
  -- `∑_{i<37} w^i = 0`: `(∑ w^i)(w − 1) = w³⁷ − 1 = 0` and `w − 1 ≠ 0` in the domain `𝓞 K`.
  have hgeom : ∑ i ∈ Finset.range 37, w ^ i = 0 := by
    have h := geom_sum_mul w 37
    rw [hw37, sub_self] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0) hw1
  -- Each `w^i ≡ 1 (mod lv149)`.
  have hpow_sub : ∀ i : ℕ, w ^ i - 1 ∈ lv149 := by
    intro i
    have hfac : w ^ i - 1 = (w - 1) * ∑ j ∈ Finset.range i, w ^ j := by
      have h := geom_sum_mul w i
      linear_combination -h
    rw [hfac]
    exact Ideal.mul_mem_right _ _ hmem
  -- Sum the congruences: `0 = ∑ w^i ≡ 37 (mod lv149)`.
  have hsum_sub : (∑ i ∈ Finset.range 37, w ^ i) -
      (∑ _i ∈ Finset.range 37, (1 : 𝓞 (CyclotomicField 37 ℚ))) ∈ lv149 := by
    rw [← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun i _ ↦ hpow_sub i
  rw [hgeom, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, zero_sub,
    neg_mem_iff] at hsum_sub
  exact caseII_thirtyseven_notMem_lv149 (by exact_mod_cast hsum_sub)

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **`1 − w ∉ lv149` for any `37`-th root of unity `w ≠ 1`** — the negated form, matching the
`(1 − ζ^k)` factors of the §9.1 factor and anchor equations. -/
theorem caseII_one_sub_root_of_unity_notMem_lv149
    {w : 𝓞 (CyclotomicField 37 ℚ)} (hw37 : w ^ 37 = 1) (hw1 : w ≠ 1) :
    1 - w ∉ lv149 := fun hmem ↦
  caseII_root_of_unity_sub_one_notMem_lv149 hw37 hw1 (neg_sub 1 w ▸ neg_mem hmem)

/-! ## 2. The Lemma-9.8 membership and the conjugate-factor exclusion over `ℓ ∣ z` data

`x + y ∈ 𝔩` is the **proven** Washington Lemma 9.8 (`caseII_real_x_add_y_mem_of_dvd_z`) at the
datum fields; subtracting it from any other conjugate factor `x + w·y ∈ 𝔩` (`w ≠ 1` a `37`-th
root) gives `(w − 1)·y ∈ 𝔩` — impossible, since `𝔩` is prime, `w − 1 ∉ 𝔩` (§1, `ℓ` unramified)
and `y ∉ 𝔩` (Lemma 9.6, datum field).  So `x + y` is the **only** conjugate factor in `𝔩`. -/

/-- **No nontrivial conjugate factor lies in `𝔩`** (proven, axiom-clean given the carried
Kellner input): for a real `ℓ ∣ z` datum and any `37`-th root of unity `w ≠ 1`,
`x + y·w ∉ lv149`. -/
theorem caseII_dvdZ_x_add_y_mul_root_notMem_lv149 {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    {w : 𝓞 (CyclotomicField 37 ℚ)} (hw37 : w ^ 37 = 1) (hw1 : w ≠ 1) :
    D.x + D.y * w ∉ lv149 := by
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  -- The PROVEN Washington Lemma 9.8 over the `ℓ ∣ z` datum: `x + y ∈ 𝔩`.
  have hsum : D.x + D.y ∈ lv149 :=
    caseII_real_x_add_y_mem_of_dvd_z hSO D.toRealCaseIIData37 D.z_mem D.x_notMem D.y_notMem
  intro hmem
  have hsub : D.y * (w - 1) ∈ lv149 := by
    have h := Ideal.sub_mem lv149 hmem hsum
    rwa [show D.x + D.y * w - (D.x + D.y) = D.y * (w - 1) by ring] at h
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hsub with hy | hwm
  · exact D.y_notMem hy
  · exact caseII_root_of_unity_sub_one_notMem_lv149 hw37 hw1 hwm

/-- **A factor generator avoids `𝔩`** (proven, axiom-clean given the carried Kellner input):
if `x + y·w = (1 − w)·c·r³⁷` in `𝓞 K` (`w ≠ 1` a `37`-th root of unity, `c` arbitrary), then
`r ∉ lv149` — else the factor `x + y·w` would land in `𝔩`, contradicting
`caseII_dvdZ_x_add_y_mul_root_notMem_lv149`. -/
theorem caseII_dvdZ_factorGenerator_notMem_lv149 {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    {w c r : 𝓞 (CyclotomicField 37 ℚ)} (hw37 : w ^ 37 = 1) (hw1 : w ≠ 1)
    (heq : D.x + D.y * w = (1 - w) * c * r ^ 37) :
    r ∉ lv149 := by
  intro hr
  refine caseII_dvdZ_x_add_y_mul_root_notMem_lv149 D hSO hw37 hw1 ?_
  rw [heq]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hr 37 (by norm_num))

/-! ## 3. Conjunct (a): `ρ₀² ∈ 𝔩` — the anchor generator inherits the `ℓ`-divisibility

Washington p. 178: from `ℓ ∣ (ω + θ)` (Lemma 9.8) and the anchor factorisation
`ω + θ = η₀·λ^{…}·ρ₀^p·(unit)` with `ℓ` unramified (`λ ∉ 𝔩`), every prime of `ℓ` divides
`ρ₀`.  Here: `x + y ∈ 𝔩` (proven Lemma 9.8), and the L1 anchor pulled back to `𝓞 K` reads
`x + y = u₀·((1−ζ)(1−ζ³⁶))^e·ρ₀³⁷`; primality of `𝔩` forces `ρ₀ ∈ 𝔩`, hence `ρ₀² ∈ 𝔩`. -/

/-- **[F2 conjunct (a)] `ρ₀² ∈ lv149`** (proven, axiom-clean given the carried Kellner input).

The exact `ρ0 ^ 2 ∈ lv149` conjunct of `CaseIIWashingtonCaseII37`, from the L1 anchor equation
(as received in the residual's antecedent). -/
theorem caseII_dvdZ_rho0_sq_mem_lv149 {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ))
    (hanchor : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
            (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37) :
    ρ0 ^ 2 ∈ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  set ζs : 𝓞 (CyclotomicField 37 ℚ) := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger
    with hζs_def
  have hζs37 : ζs ^ 37 = 1 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one
  have hζs1 : ζs ≠ 1 :=
    (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hζs36_37 : (ζs ^ 36) ^ 37 = 1 := by
    rw [pow_right_comm, hζs37, one_pow]
  have hζs36_ne1 : ζs ^ 36 ≠ 1 := fun h ↦
    (by decide : ¬ (37 : ℕ) ∣ 36)
      (((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd
        36).mp h)
  -- The anchor equation pulled back to `𝓞 K`: `x + y = u₀·((1−ζ)(1−ζ³⁶))^e·ρ₀³⁷`.
  have hint : D.x + D.y = (u0 : 𝓞 (CyclotomicField 37 ℚ)) *
      ((1 - ζs) * (1 - ζs ^ 36)) ^ e * ρ0 ^ 37 := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_pow]
    exact hanchor
  -- The PROVEN Washington Lemma 9.8: `x + y ∈ 𝔩`.
  have hsum : D.x + D.y ∈ lv149 :=
    caseII_real_x_add_y_mem_of_dvd_z hSO D.toRealCaseIIData37 D.z_mem D.x_notMem D.y_notMem
  rw [hint] at hsum
  -- `𝔩` prime: `u₀ ∉ 𝔩` (unit), `Λ ∉ 𝔩` (`ℓ` unramified), so `ρ₀³⁷ ∈ 𝔩`.
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hsum with h1 | hρ37
  · exfalso
    rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› h1 with hu | hΛe
    · exact caseII_unit_notMem_lv149 u0 hu
    · have hΛ := Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› e hΛe
      rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hΛ with h1ζ | h1ζ36
      · exact caseII_one_sub_root_of_unity_notMem_lv149 hζs37 hζs1 h1ζ
      · exact caseII_one_sub_root_of_unity_notMem_lv149 hζs36_37 hζs36_ne1 h1ζ36
  · exact Ideal.pow_mem_of_mem _
      (Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› 37 hρ37) 2 (by norm_num)

/-! ## 4. Conjunct (b): the `ω`-witnesses of `v²·ρ_a·σρ_a` avoid `𝔩`

With the integral-unit witnesses `u_a` (factor unit) and `vU` (Assumption-II unit), the factor
generator `ρ_a = algebraMap r_a` is integral (`caseII_factorGenerator_integral_of_unitInt`),
and any witness `ω` of `v²·ρ_a·σρ_a` equals `vU²·r_a·σr_a` in `𝓞 K`.  Were `ω ∈ 𝔩`: `𝔩` prime
and `vU ∉ 𝔩` force `r_a ∈ 𝔩` or `σr_a ∈ 𝔩`; the integral factor equation
`x + y·ζ = (1−ζ)·u_a·r_a³⁷` (or its `σ`-transport at `ζ³⁶`, using `σx = x`, `σy = y`,
`σζ = ζ³⁶`) then puts the conjugate factor `x + ζ^{±1}·y` into `𝔩` — excluded by §2. -/

/-- **[F2 conjunct (b)] every integer witness of `v²·ρ_a·σρ_a` avoids `lv149`** (proven,
axiom-clean given the carried Kellner input).

The exact `∀ ω`-conjunct of `CaseIIWashingtonCaseII37`, with the integral-unit witnesses
`u_a` (for the factor unit `η_a`) and `vU` (for the Assumption-II unit `v`) supplied. -/
theorem caseII_dvdZ_omega_witness_notMem_lv149 {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    (ηa v : (CyclotomicField 37 ℚ)ˣ) (ρa : CyclotomicField 37 ℚ)
    (ua vU : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hvU : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (vU : 𝓞 _) =
      (v : CyclotomicField 37 ℚ))
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) :
    ∀ ω : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
        (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) →
      ω ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  set ζ : 𝓞 (CyclotomicField 37 ℚ) := D.hζ.toInteger with hζ_def
  have hζ37 : ζ ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hζ1 : ζ ≠ 1 := D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hζ36_37 : (ζ ^ 36) ^ 37 = 1 := by
    rw [pow_right_comm, hζ37, one_pow]
  have hζ36_ne1 : ζ ^ 36 ≠ 1 := fun h ↦
    (by decide : ¬ (37 : ℕ) ∣ 36) ((D.hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd 36).mp h)
  -- `ρ_a` is integral (factor unit integral).
  have hηmem : ζ ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
  have hetaZero : (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) = 1 :=
    caseII_etaZero_eq_one D.toRealCaseIIData37 hp
  have hηne : (⟨ζ, hηmem⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) ≠
      D.etaZero := by
    intro h
    refine hζ1 ?_
    have := Subtype.ext_iff.mp h
    rwa [hetaZero] at this
  obtain ⟨ra, hra⟩ := caseII_factorGenerator_integral_of_unitInt D.toRealCaseIIData37
    ⟨ζ, hηmem⟩ hηne ηa ρa ua hua (by
      rw [show ((⟨ζ, hηmem⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
        𝓞 (CyclotomicField 37 ℚ)) = ζ from rfl]
      exact hfa)
  -- The integral positive factor equation `x + y·ζ = (1−ζ)·u_a·r_a³⁷`.
  have hint : D.x + D.y * ζ =
      (1 - ζ) * (ua : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37 := by
    apply hinj
    push_cast [map_add, map_mul, map_sub, map_one, map_pow, hua, hra]
    linear_combination hfa
  -- The σ-transport: `x + y·ζ³⁶ = (1−ζ³⁶)·σ(u_a)·(σr_a)³⁷` (`x, y` real, `σζ = ζ³⁶`).
  have hσint : D.x + D.y * ζ ^ 36 =
      (1 - ζ ^ 36) * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (ua : 𝓞 _) *
        (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ra) ^ 37 := by
    have h := congrArg (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)) hint
    rwa [caseII_ringOfIntegersComplexConj_x_add_y_mul D.x_real D.y_real,
      map_mul, map_mul, map_sub, map_one, map_pow,
      caseII_ringOfIntegersComplexConj_root_of_unity hζ37] at h
  -- `algebraMap (σ r_a) = σ ρ_a`.
  have hσra : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
      (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ra) =
      complexConj (CyclotomicField 37 ℚ) ρa := by
    rw [← hra]
    exact coe_ringOfIntegersComplexConj (K := CyclotomicField 37 ℚ) ra
  intro ω hω hmem
  -- `ω = vU²·(r_a·σr_a)` in `𝓞 K`.
  have hω_int : ω = (vU : 𝓞 (CyclotomicField 37 ℚ)) ^ 2 *
      (ra * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ra) := by
    apply hinj
    rw [hω, map_mul, map_pow, map_mul, hvU, hra, hσra]
  rw [hω_int] at hmem
  -- `𝔩` prime: `vU ∈ 𝔩` (unit — impossible), `r_a ∈ 𝔩`, or `σr_a ∈ 𝔩`.
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hmem with hv2 | hprod
  · exact caseII_unit_notMem_lv149 vU (Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› 2 hv2)
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hprod with hra_mem | hσra_mem
  · exact caseII_dvdZ_factorGenerator_notMem_lv149 D hSO hζ37 hζ1 hint hra_mem
  · exact caseII_dvdZ_factorGenerator_notMem_lv149 D hSO hζ36_37 hζ36_ne1 hσint hσra_mem

/-- **[F2 conjunct (b), Assumption-II form]** the `∀ ω`-conjunct with the Assumption-II tie
`η_a = v³⁷·η_b` in place of the direct integral witness for `v` (the witness is derived via
`caseII_assumptionII_unit_integral`). -/
theorem caseII_dvdZ_omega_witness_notMem_lv149_of_assumptionII {m : ℕ}
    (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    (ηa ηb v : (CyclotomicField 37 ℚ)ˣ) (ρa : CyclotomicField 37 ℚ)
    (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hub : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
      (ηb : CyclotomicField 37 ℚ))
    (hII : (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb)
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37) :
    ∀ ω : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
        (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) →
      ω ∉ lv149 := by
  obtain ⟨vU, hvU⟩ := caseII_assumptionII_unit_integral ηa ηb v ua ub hua hub hII
  exact caseII_dvdZ_omega_witness_notMem_lv149 D hSO ηa v ρa ua vU hua hvU hfa

/-! ## 5. Conjunct (c): the `θ`-witnesses of `−ρ_b·σρ_b` avoid `𝔩`

Identical mechanism at the root `ζ²`: `r_b` integral from `u_b`, `θ = −r_b·σr_b`, and a
membership `θ ∈ 𝔩` would force the conjugate factor `x + ζ^{±2}·y` into `𝔩` — excluded. -/

/-- **[F2 conjunct (c)] every integer witness of `−ρ_b·σρ_b` avoids `lv149`** (proven,
axiom-clean given the carried Kellner input).

The exact `∀ θ`-conjunct of `CaseIIWashingtonCaseII37`, with the integral-unit witness `u_b`
for the factor unit `η_b` supplied. -/
theorem caseII_dvdZ_theta_witness_notMem_lv149 {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    (ηb : (CyclotomicField 37 ℚ)ˣ) (ρb : CyclotomicField 37 ℚ)
    (ub : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hub : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
      (ηb : CyclotomicField 37 ℚ))
    (hfb : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
        (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) :
    ∀ θ : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
        -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) →
      θ ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  set ζ : 𝓞 (CyclotomicField 37 ℚ) := D.hζ.toInteger with hζ_def
  have hζ37 : ζ ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hζ2_37 : (ζ ^ 2) ^ 37 = 1 := by
    rw [pow_right_comm, hζ37, one_pow]
  have hζ2_1 : ζ ^ 2 ≠ 1 := fun h ↦
    (by decide : ¬ (37 : ℕ) ∣ 2) ((D.hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd 2).mp h)
  have hζ2_36_37 : ((ζ ^ 2) ^ 36) ^ 37 = 1 := by
    rw [pow_right_comm, hζ2_37, one_pow]
  have hζ2_36_ne1 : (ζ ^ 2) ^ 36 ≠ 1 := fun h ↦ by
    rw [← pow_mul] at h
    exact (by decide : ¬ (37 : ℕ) ∣ 2 * 36)
      ((D.hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd (2 * 36)).mp h)
  -- `ρ_b` is integral (factor unit integral).
  have hηmem2 : ζ ^ 2 ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    (mem_nthRootsFinset (by norm_num) _).mpr hζ2_37
  have hetaZero : (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) = 1 :=
    caseII_etaZero_eq_one D.toRealCaseIIData37 hp
  have hηne2 : (⟨ζ ^ 2, hηmem2⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) ≠
      D.etaZero := by
    intro h
    refine hζ2_1 ?_
    have := Subtype.ext_iff.mp h
    rwa [hetaZero] at this
  obtain ⟨rb, hrb⟩ := caseII_factorGenerator_integral_of_unitInt D.toRealCaseIIData37
    ⟨ζ ^ 2, hηmem2⟩ hηne2 ηb ρb ub hub (by
      rw [show ((⟨ζ ^ 2, hηmem2⟩ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
        𝓞 (CyclotomicField 37 ℚ)) = ζ ^ 2 from rfl]
      exact hfb)
  -- The integral positive factor equation `x + y·ζ² = (1−ζ²)·u_b·r_b³⁷`.
  have hint : D.x + D.y * ζ ^ 2 =
      (1 - ζ ^ 2) * (ub : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37 := by
    have hfb2 := hfb
    rw [map_pow] at hfb2
    apply hinj
    push_cast [map_add, map_mul, map_sub, map_one, map_pow, hub, hrb]
    linear_combination hfb2
  -- The σ-transport: `x + y·(ζ²)³⁶ = (1−(ζ²)³⁶)·σ(u_b)·(σr_b)³⁷`.
  have hσint : D.x + D.y * (ζ ^ 2) ^ 36 =
      (1 - (ζ ^ 2) ^ 36) * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (ub : 𝓞 _) *
        (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rb) ^ 37 := by
    have h := congrArg (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)) hint
    rwa [caseII_ringOfIntegersComplexConj_x_add_y_mul D.x_real D.y_real,
      caseII_ringOfIntegersComplexConj_root_of_unity hζ2_37,
      map_mul, map_mul, map_sub, map_one,
      caseII_ringOfIntegersComplexConj_root_of_unity hζ2_37, map_pow] at h
  -- `algebraMap (σ r_b) = σ ρ_b`.
  have hσrb : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
      (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rb) =
      complexConj (CyclotomicField 37 ℚ) ρb := by
    rw [← hrb]
    exact coe_ringOfIntegersComplexConj (K := CyclotomicField 37 ℚ) rb
  intro θ hθ hmem
  -- `θ = −(r_b·σr_b)` in `𝓞 K`.
  have hθ_int : θ = -(rb * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rb) := by
    apply hinj
    rw [hθ, map_neg, map_mul, hrb, hσrb]
  rw [hθ_int, neg_mem_iff] at hmem
  -- `𝔩` prime: `r_b ∈ 𝔩` or `σr_b ∈ 𝔩` — both excluded.
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hmem with hrb_mem | hσrb_mem
  · exact caseII_dvdZ_factorGenerator_notMem_lv149 D hSO hζ2_37 hζ2_1 hint hrb_mem
  · exact caseII_dvdZ_factorGenerator_notMem_lv149 D hSO hζ2_36_37 hζ2_36_ne1 hσint hσrb_mem

/-! ## 6. The packaged `ℓ`-propagation triple, and the full residual conclusion

`caseII_dvdZ_ellPropagation_withUnits` packages (a) ∧ (b) ∧ (c) in the residual's exact
conjunct shapes; `caseII_dvdZ_caseII_conclusion_of_realAssumptionII` then produces the **full
`∃ v`-conclusion** of `CaseIIWashingtonCaseII37` from a real Assumption-II witness.  So, given
the integral-unit witnesses, the clean residual's conclusion is reduced to **real Assumption II
alone** — the `ℓ`-propagation is retired. -/

/-- **[F2 — the `ℓ`-propagation triple]** conjuncts (a) ∧ (b) ∧ (c) of
`CaseIIWashingtonCaseII37`, in their exact shapes, from the with-units factor data, the
Assumption-II tie, and the anchor (proven, axiom-clean given the carried Kellner input). -/
theorem caseII_dvdZ_ellPropagation_withUnits {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    (ηa ηb v : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ)
    (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hub : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
      (ηb : CyclotomicField 37 ℚ))
    (hII : (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb)
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37)
    (hfb : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
        (ηb : CyclotomicField 37 ℚ) * ρb ^ 37)
    (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ))
    (hanchor : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
            (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37) :
    ρ0 ^ 2 ∈ lv149 ∧
    (∀ ω : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
          (v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa) →
      ω ∉ lv149) ∧
    (∀ θ : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
          -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) →
      θ ∉ lv149) :=
  ⟨caseII_dvdZ_rho0_sq_mem_lv149 D hSO e u0 ρ0 hanchor,
    caseII_dvdZ_omega_witness_notMem_lv149_of_assumptionII D hSO ηa ηb v ρa ua ub hua hub
      hII hfa,
    caseII_dvdZ_theta_witness_notMem_lv149 D hSO ηb ρb ub hub hfb⟩

/-- **[F2 — the full residual conclusion from real Assumption II]** the exact `∃ v`-conclusion
of `CaseIIWashingtonCaseII37`, from a **real Assumption-II witness** (`σv = v`,
`η_a = v³⁷·η_b`) and the with-units factor data + anchor (proven, axiom-clean given the carried
Kellner input).  Given the integral-unit witnesses, the clean residual's conclusion rests on
real Assumption II alone — the aux-prime `ℓ`-propagation is PROVEN, not carried. -/
theorem caseII_dvdZ_caseII_conclusion_of_realAssumptionII {m : ℕ}
    (D : RealCaseIIDvdZData37 m)
    (hSO : NoSecondOrderIrregularPair 37 32)
    (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ)
    (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hua : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ua : 𝓞 _) =
      (ηa : CyclotomicField 37 ℚ))
    (hub : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ub : 𝓞 _) =
      (ηb : CyclotomicField 37 ℚ))
    (hfa : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
        (ηa : CyclotomicField 37 ℚ) * ρa ^ 37)
    (hfb : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
      (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
        (ηb : CyclotomicField 37 ℚ) * ρb ^ 37)
    (e : ℕ) (u0 : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ))
    (hanchor : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
            (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37)
    (v : (CyclotomicField 37 ℚ)ˣ)
    (hv_real : complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
      (v : CyclotomicField 37 ℚ))
    (hII : (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb) :
    ∃ v' : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v' : CyclotomicField 37 ℚ) =
          (v' : CyclotomicField 37 ℚ) ∧
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v' ^ 37 * ηb ∧
      ρ0 ^ 2 ∈ lv149 ∧
      (∀ ω : 𝓞 (CyclotomicField 37 ℚ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ω =
            (v' : CyclotomicField 37 ℚ) ^ 2 *
              (ρa * complexConj (CyclotomicField 37 ℚ) ρa) →
        ω ∉ lv149) ∧
      (∀ θ : 𝓞 (CyclotomicField 37 ℚ),
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) θ =
            -(ρb * complexConj (CyclotomicField 37 ℚ) ρb) →
        θ ∉ lv149) := by
  obtain ⟨ha, hb, hc⟩ := caseII_dvdZ_ellPropagation_withUnits D hSO ηa ηb v ρa ρb ua ub
    hua hub hII hfa hfb e u0 ρ0 hanchor
  exact ⟨v, hv_real, hII, ha, hb, hc⟩

end BernoulliRegular.FLT37.Eichler

end

end

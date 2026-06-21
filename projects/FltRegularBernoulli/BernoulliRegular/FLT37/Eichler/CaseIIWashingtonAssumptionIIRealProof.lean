import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonCaseIIClean
import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonEllPropagation
import BernoulliRegular.FLT37.Eichler.CaseIIModuloKellner

/-!
# [F1] Real Assumption II for the §9.1 factor units, PROVEN (route (a), Washington Lemma 9.9)

This file **discharges the real-Assumption-II conjunct** of the clean Case-II residual
`CaseIIWashingtonCaseII37` (`CaseIIWashingtonCaseIIClean.lean`), i.e. it **proves**
`CaseIIWashingtonAssumptionIIReal37` (`CaseIIWashingtonDescentClose.lean`) from the carried
Kellner input `NoSecondOrderIrregularPair 37 32` alone: for a real `ℓ ∣ z` datum
`D : RealCaseIIDvdZData37 m` with coprime Fermat variables, **every** choice of real factor units
`η_a, η_b : Kˣ` and generators `ρ_a, ρ_b : K` satisfying the two §9.1 factor equations at `ζ, ζ²`
admits a **real** unit `v : Kˣ` with `η_a = v³⁷·η_b`.

## The proof (Washington, GTM 83, Lemma 9.9, p. 180 — every deep ingredient already PROVEN)

1. **Integral normalisation.**  The proven strengthened L2 producer
   (`caseII_section91_factorEquations_etaOne_etaTwo_withUnits`) supplies one specific choice
   `η_a⁰ = algebraMap u_a`, `η_b⁰ = algebraMap u_b` with **integral** units `u_a, u_b : (𝓞 K)ˣ`
   and integral generators `r_a, r_b` (`caseII_factorGenerator_integral_of_unitInt`).  Any other
   choice `(η_a, ρ_a)` satisfying the same factor equation differs by an explicit `37`-th power:
   `η_a = η_a⁰·(ρ_a⁰/ρ_a)³⁷` (cancel `1 − ζ ≠ 0`, `ρ_a ≠ 0`).  So real Assumption II for the given
   `η_a/η_b` reduces to the **global `37`-th-power property of the integral ratio `u_a/u_b`**.

2. **The genuine three-term §9.1 descent instance** (`caseII_washington_threeTermInstance`).
   Washington's identity `x + ζ²y = (1+ζ)(x+ζy) − ζ(x+y)`, the two integral factor equations,
   the proven L1 anchor `x + y = u₀·Λ^e·ρ₀³⁷` (`caseII_anchor_real_rho0_genuineUnit`), the span
   identity `(Λ) = 𝔭²` (`caseII_span_lambda_eq_p_sq`), and the proven anchor-exponent identity
   `2e = 37m + 1` (`caseII_anchor_exponent_eq`) combine — after cancelling one `(1−ζ)` — into a
   **genuine Case-II descent equation**

   `((1+ζ)u_a)·r_a³⁷ + (−(1+ζ)u_b)·r_b³⁷ = ε₃·((ζ−1)^m·ρ₀)³⁷`,

   an instance of exactly the shape consumed by the proven Corollary-8.15 machinery, with
   `ε₁/ε₂ = −(u_a/u_b)` and the `𝔭`-coprimalities `(ζ−1) ∤ r_a, r_b, ρ₀` all proven
   (`caseII_zeta_sub_one_not_dvd_factorGenerator`, `(ρ₀) = B₀` + `not_p_div_a_zero`).

3. **Single-index expansion** (PROVEN): `caseII_corollary815_singleIndexExpansion37_proven`
   (`CaseIIModuloKellner.lean`, via the unconditional R3 residue equations) applied to this
   instance gives `−(u_a/u_b) = E₃₂^d·α³⁷`.

4. **Local power mod `𝔩 = lv149`** (`caseII_washington_factorRatio_localPower`): the proven
   Washington Lemma 9.8 over real data (`caseII_real_x_add_y_mem_of_dvd_z`, from the Mirimanoff
   step-6 reality core, under `hSO`) gives `x + y ∈ 𝔩`, so `Q(y) = −Q(x)` and the factor
   equations collapse mod `𝔩` to `Q(u_a)·Q(r_a)³⁷ = Q(x) = Q(u_b)·Q(r_b)³⁷` (the `(1−ζ^a)`
   cancellation of Lemma 9.9, `1 − ζ, 1 − ζ² ∉ 𝔩`).  Hence
   `Q(ε₁/ε₂) = −(Q(r_b)/Q(r_a))³⁷` is a `37`-th power mod `𝔩` (`−1 = (−1)³⁷`).

5. **The collapse** (PROVEN): `caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`
   (`CaseIIAssumptionII.lean`, operative core `ind₃₇ E₃₂ ≠ 0` from the worked certificate)
   upgrades local + single-index to **global**: `−(u_a/u_b) = ε'³⁷`, so `u_a/u_b = (−ε')³⁷`.

6. **Real `37`-th root** (`caseII_washington_real_root_of_pow_real`): `η_a/η_b = T³⁷` with
   `T = −(algebraMap ε')·(ρ_a⁰ ρ_b)/(ρ_a ρ_b⁰)`; reality of `η_a, η_b` makes `σ(T³⁷) = T³⁷`, so
   `σT/T` is a `37`-th root of unity `ζ^j`, and `v := ζ^{19j}·T` is **real** (`2·19 ≡ 1 (mod 37)`
   kills the `ζ`-twist) with `v³⁷ = T³⁷`.  Hence `η_a = v³⁷·η_b` with `v` real.

Combined with the parallel F2 `ℓ`-propagation file (`CaseIIWashingtonEllPropagation.lean`), §7
then proves the **with-units `p`-content extraction data** outright
(`caseIISection91PContentExtractionDataWithUnits37_proven`) and re-closes the FLT37 endpoint with
the clean Case-II residual **fully retired**
(`fermatLastTheoremFor_thirtyseven_of_lemma96_coprimality`: FLT37 from coprimality + Washington
Lemma 9.6 + Kellner only).

No `sorry`, no axioms beyond `propext, Classical.choice, Quot.sound`.  This file imports only —
it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83: §9.1 (pp. 169–173, the factor
  equations and the three-term reassembly), Lemma 9.8 (p. 180, `ℓ ∣ ω + θ`), Lemma 9.9
  (pp. 180–181, `η_a/η_b ≡ (ρ_b/ρ_a)^p (mod 𝔩)` and the index collapse), Proposition 1.5
  (the `ζ^k`-absorption of real units).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The real `37`-th root: absorbing the `ζ`-twist (Washington Prop. 1.5 mechanism)

If `t³⁷` (as a field element) is fixed by complex conjugation, then `σt/t` is a `37`-th root of
unity `ζ^j`, and `v = ζ^{19j}·t` satisfies `σv = v` (since `2·19 ≡ 1 (mod 37)`) and `v³⁷ = t³⁷`. -/

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)] in
/-- **The real `37`-th root of a conjugation-fixed `37`-th power.**  For `t : Kˣ` with
`σ(t³⁷) = t³⁷` (`σ` the complex conjugation of the CM field `K = ℚ(ζ₃₇)`), there is a **real**
unit `v : Kˣ` with `v³⁷ = t³⁷`.

The deviation `τ = σ(t)/t` satisfies `τ³⁷ = 1`, so `τ = ζ^j`; the twist is absorbed by
`v = ζ^{19j}·t`: `σv = ζ^{36·19j}·ζ^j·t = ζ^{19j}·t = v` (as `36·19j + j ≡ 19j (mod 37)`), and
`ζ^{37·19j} = 1` keeps the `37`-th power. -/
theorem caseII_washington_real_root_of_pow_real
    {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37) (t : (CyclotomicField 37 ℚ)ˣ)
    (hreal : complexConj (CyclotomicField 37 ℚ) ((t : CyclotomicField 37 ℚ) ^ 37) =
      (t : CyclotomicField 37 ℚ) ^ 37) :
    ∃ v : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
        (v : CyclotomicField 37 ℚ) ∧ v ^ 37 = t ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  have ht_ne : (t : CyclotomicField 37 ℚ) ≠ 0 := Units.ne_zero t
  -- The deviation `τ = σ(t)/t` is a `37`-th root of unity.
  have hτ37 : (complexConj (CyclotomicField 37 ℚ) (t : CyclotomicField 37 ℚ) /
      (t : CyclotomicField 37 ℚ)) ^ 37 = 1 := by
    rw [div_pow, ← map_pow, hreal, div_self (pow_ne_zero _ ht_ne)]
  obtain ⟨j, _, hjτ⟩ := hζ.eq_pow_of_pow_eq_one hτ37
  have hστ : complexConj (CyclotomicField 37 ℚ) (t : CyclotomicField 37 ℚ) =
      ζ ^ j * (t : CyclotomicField 37 ℚ) := by
    rw [hjτ]
    exact (div_mul_cancel₀ _ ht_ne).symm
  -- `σ ζ = ζ³⁶` (conjugation inverts roots of unity).
  have hζcoe : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) hζ.toInteger = ζ := rfl
  have hσζ : complexConj (CyclotomicField 37 ℚ) ζ = ζ ^ 36 := by
    rw [← hζcoe, ← coe_ringOfIntegersComplexConj,
      caseII_ringOfIntegersComplexConj_root_of_unity hζ.toInteger_isPrimitiveRoot.pow_eq_one]
    exact map_pow (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) _ 36
  have hζu : IsUnit ζ := hζ.isUnit (by decide)
  refine ⟨hζu.unit ^ (19 * j) * t, ?_, ?_⟩
  · -- reality of `v = ζ^{19j}·t`.
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hζu.unit_spec, map_mul, map_pow, hσζ, hστ,
      ← pow_mul, ← mul_assoc, ← pow_add,
      show 36 * (19 * j) + j = 37 * (18 * j) + 19 * j from by ring, pow_add, pow_mul,
      hζ.pow_eq_one, one_pow, one_mul]
  · -- `v³⁷ = t³⁷`.
    have hu37 : hζu.unit ^ 37 = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, hζu.unit_spec, hζ.pow_eq_one, Units.val_one]
    rw [mul_pow, ← pow_mul, show 19 * j * 37 = 37 * (19 * j) from by ring, pow_mul, hu37,
      one_pow, one_mul]

/-! ## 2. The `(1+ζ)`-unit

`1 + ζ = (ζ² − 1)/(ζ − 1)` is a (cyclotomic) unit of `𝓞 K`: both `ζ − 1` and `ζ² − 1` are
`𝔭`-uniformisers (`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`). -/

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **`1 + ζ` is a unit of `𝓞 K`.**  From `Associated (ζ − 1) (ζ² − 1)` and
`(ζ − 1)(ζ + 1) = ζ² − 1`, cancelling `ζ − 1 ≠ 0`. -/
theorem caseII_washington_one_add_zeta_unit
    {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37) :
    ∃ εp : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      (εp : 𝓞 (CyclotomicField 37 ℚ)) = hζ.toInteger + 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hmem_one : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) := one_mem_nthRootsFinset (by norm_num)
  have hmem_sq : hζ.toInteger ^ 2 ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    (mem_nthRootsFinset (by norm_num) _).mpr (by
      rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow])
  have hne : hζ.toInteger ^ 2 ≠ (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
  have hassoc : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) (hζ.toInteger ^ 2 - 1) :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hmem_sq hmem_one hne
  obtain ⟨εp, hεp⟩ := hassoc
  refine ⟨εp, ?_⟩
  have hζ_ne : (hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 :=
    sub_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37))
  apply mul_left_cancel₀ hζ_ne
  rw [hεp]; ring

/-! ## 3. The three-term §9.1 descent instance from the factor equations + the anchor

Washington's identity `x + ζ²y = (1+ζ)(x+ζy) − ζ(x+y)` (GTM 83, p. 168) reassembles the two
integral factor equations and the anchor equation — `Λ^e = (ζ−1)^{2e}·w'^e` with the proven
`2e = 37m+1` — into a genuine Case-II descent equation at level `m`, after cancelling `(1−ζ)`. -/

/-- **The §9.1 three-term descent instance** (proven, axiom-clean).  From the two integral factor
equations at `ζ, ζ²`, the integral anchor equation, and `2e = 37m+1`, the integral data form a
Case-II descent equation

  `((1+ζ)·u_a)·r_a³⁷ + (−(1+ζ)·u_b)·r_b³⁷ = ε₃·((ζ−1)^m·ρ₀)³⁷`

for a unit `ε₃` (`= −ζ·u₀·w'^e`, `w'` the unit with `(ζ−1)²·w' = Λ`). -/
theorem caseII_washington_threeTermInstance
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (ua ub u0 εp : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ra rb ρ0 : 𝓞 (CyclotomicField 37 ℚ)) (e : ℕ)
    (hεp : (εp : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger + 1)
    (hFa : D.x + D.hζ.toInteger * D.y =
      (1 - D.hζ.toInteger) * (ua : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37)
    (hFb : D.x + D.hζ.toInteger ^ 2 * D.y =
      (1 - D.hζ.toInteger ^ 2) * (ub : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37)
    (hanchor : D.x + D.y = (u0 : 𝓞 (CyclotomicField 37 ℚ)) *
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ e * ρ0 ^ 37)
    (h2e : 2 * e = 37 * m + 1) :
    ∃ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      ((εp * ua : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37 +
          ((-(εp * ub) : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * ρ0) ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `Λ = (ζ−1)²·w'` for a unit `w'` (the span identity `(Λ) = 𝔭²`).
  have hspan := caseII_span_lambda_eq_p_sq D.hζ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ))
  rw [Ideal.span_singleton_pow] at hspan
  obtain ⟨w', hw'⟩ : Associated ((D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2)
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan.symm
  -- The anchor with the `(ζ−1)`-power split out: `x+y = u₀·((ζ−1)^{37m}·((ζ−1)·w'^e))·ρ₀³⁷`.
  have hanchor' : D.x + D.y = (u0 : 𝓞 (CyclotomicField 37 ℚ)) *
      ((D.hζ.toInteger - 1) ^ (37 * m) *
        ((D.hζ.toInteger - 1) * (w' : 𝓞 (CyclotomicField 37 ℚ)) ^ e)) * ρ0 ^ 37 := by
    rw [hanchor, ← hw', mul_pow, ← pow_mul, h2e]
    ring
  -- `1 − ζ ≠ 0`.
  have hζ_ne : (1 : 𝓞 (CyclotomicField 37 ℚ)) - D.hζ.toInteger ≠ 0 := by
    intro h
    exact D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) (by linear_combination -h)
  -- The key identity, before cancelling `(1−ζ)` (Washington's three-term identity).
  have key : (1 - D.hζ.toInteger) *
      ((D.hζ.toInteger + 1) * (ub : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37) =
      (1 - D.hζ.toInteger) *
        ((D.hζ.toInteger + 1) * (ua : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37 +
          D.hζ.toInteger * (u0 : 𝓞 (CyclotomicField 37 ℚ)) *
            (w' : 𝓞 (CyclotomicField 37 ℚ)) ^ e * (D.hζ.toInteger - 1) ^ (37 * m) * ρ0 ^ 37) := by
    linear_combination (D.hζ.toInteger + 1) * hFa - hFb - D.hζ.toInteger * hanchor'
  have key' := mul_left_cancel₀ hζ_ne key
  refine ⟨-((D.hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit * u0 * w' ^ e), ?_⟩
  simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, IsUnit.unit_spec, hεp]
  linear_combination -key'

/-! ## 4. The Lemma-9.9 local power of the integral factor-unit ratio, mod `𝔩 = lv149`

With `x + y ∈ 𝔩` (the **proven** Washington Lemma 9.8 over real data,
`caseII_real_x_add_y_mem_of_dvd_z`), the two integral factor equations collapse mod `𝔩` to
`Q(u_a)·Q(r_a)³⁷ = Q(x) = Q(u_b)·Q(r_b)³⁷` (the `(1 − ζ^a)`-cancellation of Lemma 9.9), so the
descent ratio `ε₁/ε₂ = −(u_a/u_b)` is a `37`-th power mod `𝔩` (`−1 = (−1)³⁷`). -/

/-- **The Lemma-9.9 local power of `ε₁/ε₂ = (εp·u_a)/(−(εp·u_b))` mod `lv149`** (proven,
axiom-clean, under the carried Kellner input).  Washington's
`η_a/η_b ≡ (ρ_b/ρ_a)³⁷ (mod 𝔩)` for the integral factor data. -/
theorem caseII_washington_factorRatio_localPower
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (ua ub εp : (𝓞 (CyclotomicField 37 ℚ))ˣ) (ra rb : 𝓞 (CyclotomicField 37 ℚ))
    (hεp : (εp : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger + 1)
    (hFa : D.x + D.hζ.toInteger * D.y =
      (1 - D.hζ.toInteger) * (ua : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37)
    (hFb : D.x + D.hζ.toInteger ^ 2 * D.y =
      (1 - D.hζ.toInteger ^ 2) * (ub : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      (((εp * ua) / (-(εp * ub)) : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set Q := Ideal.Quotient.mk lv149 with hQ
  -- Washington Lemma 9.8 over real data (proven): `x + y ∈ 𝔩`.
  have hxy : D.x + D.y ∈ lv149 :=
    caseII_real_x_add_y_mem_of_dvd_z hSO D.toRealCaseIIData37 D.z_mem D.x_notMem D.y_notMem
  have hQy : Q D.y = -Q D.x := by
    have h0 : Q (D.x + D.y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxy
    rw [map_add] at h0
    linear_combination h0
  have hQx : Q D.x ≠ 0 := fun h => D.x_notMem (Ideal.Quotient.eq_zero_iff_mem.mp h)
  -- `1 − Q(ζ) ≠ 0` and `1 − Q(ζ)² ≠ 0` (`𝔩` is unramified, `1+ζ` is a unit).
  have hQζ1 : (1 : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) - Q D.hζ.toInteger ≠ 0 := by
    intro h0
    refine caseII_zeta_sub_one_notMem_lv149 D.hζ (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    rw [map_sub, map_one]
    linear_combination -h0
  have hQζ2 : (1 : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) - Q D.hζ.toInteger ^ 2 ≠ 0 := by
    intro h0
    have hmul : Q (D.hζ.toInteger - 1) * Q (εp : 𝓞 (CyclotomicField 37 ℚ)) = 0 := by
      rw [← map_mul, show (D.hζ.toInteger - 1) * (εp : 𝓞 (CyclotomicField 37 ℚ)) =
        D.hζ.toInteger ^ 2 - 1 from by rw [hεp]; ring, map_sub, map_pow, map_one]
      linear_combination -h0
    rcases mul_eq_zero.mp hmul with h1 | h2
    · exact caseII_zeta_sub_one_notMem_lv149 D.hζ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    · exact caseII_unit_notMem_lv149 εp (Ideal.Quotient.eq_zero_iff_mem.mp h2)
  -- The `(1−ζ^a)`-cancelled residue forms of the two factor equations.
  have hE1 : Q (ua : 𝓞 (CyclotomicField 37 ℚ)) * Q ra ^ 37 = Q D.x := by
    have h := congrArg Q hFa
    simp only [map_add, map_mul, map_pow, map_sub, map_one] at h
    rw [hQy] at h
    refine mul_left_cancel₀ hQζ1 ?_
    linear_combination -h
  have hE2 : Q (ub : 𝓞 (CyclotomicField 37 ℚ)) * Q rb ^ 37 = Q D.x := by
    have h := congrArg Q hFb
    simp only [map_add, map_mul, map_pow, map_sub, map_one] at h
    rw [hQy] at h
    refine mul_left_cancel₀ hQζ2 ?_
    linear_combination -h
  -- Nonvanishing of the residues.
  have hQra : Q ra ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero] at hE1
    exact hQx hE1.symm
  have hQε₂ : Q ((-(εp * ub) : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 :=
    fun h => caseII_unit_notMem_lv149 (-(εp * ub)) (Ideal.Quotient.eq_zero_iff_mem.mp h)
  -- The division identity `Q(ε₁/ε₂)·Q(ε₂) = Q(ε₁)`.
  have hunit : ((εp * ua) / (-(εp * ub)) : (𝓞 (CyclotomicField 37 ℚ))ˣ) * (-(εp * ub)) =
      εp * ua := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hQdiv : Q (((εp * ua) / (-(εp * ub)) : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
        𝓞 (CyclotomicField 37 ℚ)) *
      Q ((-(εp * ub) : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) =
      Q ((εp * ua : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← map_mul, ← Units.val_mul, hunit]
  -- The explicit `37`-th-root witness `−(Q r_b·(Q r_a)⁻¹)`.
  refine ⟨-(Q rb * (Q ra)⁻¹), mul_right_cancel₀ hQε₂ ?_⟩
  rw [hQdiv, Odd.neg_pow (by decide : Odd 37), mul_pow, inv_pow]
  simp only [Units.val_mul, Units.val_neg, map_mul, map_neg]
  field_simp
  linear_combination Q (εp : 𝓞 (CyclotomicField 37 ℚ)) * hE1 -
    Q (εp : 𝓞 (CyclotomicField 37 ℚ)) * hE2

/-! ## 4b. The algebraic-descent core and the assembly helpers of the main theorem

Three private helpers carve the §9.1 real-Assumption-II argument into its three independent stages,
so the main theorem reads as the outline §A–§K:

* `caseII_washington_etaZero_descent` (§A–§G) — the **algebraic descent**: from the integral L2
  producer, the `(1+ζ)`-unit, the L1 anchor, the three-term §9.1 reassembly, the proven
  Corollary-8.15 single-index expansion, the Lemma-9.9 local power, and the proven discrete-log
  collapse, it produces a normalised integral representation `(η_a⁰,ρ_a⁰), (η_b⁰,ρ_b⁰)` of the two
  factor equations whose factor-unit ratio is `−(37`-th power`)`: `η_a⁰ = −T₀³⁷·η_b⁰`.
* `caseII_washington_factorRepresentation_pow_eq` (§H) — the **representation comparison**: any two
  unit/generator pairs satisfying the same factor equation `x+ζ^a y = (1−ζ^a)·η·ρ³⁷` (nonzero RHS)
  have nonzero generators and equal `η·ρ³⁷`.
* `caseII_washington_realRoot_of_factorRatio` (§I–§K) — the **real root**: from the two comparisons
  and `η_a⁰ = −T₀³⁷·η_b⁰`, the combined root `T = −T₀·(ρ_a⁰ρ_b)/(ρ_aρ_b⁰)` gives `η_a/η_b = T³⁷`,
  conjugation-fixed by reality of `η_a, η_b`, whose real `37`-th root (the `ζ^{19j}`-absorption)
  is the required `v`. -/

/-- **Algebraic descent (§A–§G), axiom-clean** under the carried Kellner input.  From coprime real
`ℓ ∣ z` data, the §9.1 machinery yields a normalised integral factor representation
`(η_a⁰,ρ_a⁰), (η_b⁰,ρ_b⁰)` — both factor units real and integral — whose ratio is minus a
`37`-th power: `η_a⁰ = −T₀³⁷·η_b⁰`, with `T₀ = algebraMap ε'` the image of the descent unit. -/
private theorem caseII_washington_etaZero_descent
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (ηa₀ ηb₀ : (CyclotomicField 37 ℚ)ˣ) (ρa₀ ρb₀ T₀ : CyclotomicField 37 ℚ),
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger)) *
          (ηa₀ : CyclotomicField 37 ℚ) * ρa₀ ^ 37) ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2)) *
          (ηb₀ : CyclotomicField 37 ℚ) * ρb₀ ^ 37) ∧
      (ηa₀ : CyclotomicField 37 ℚ) = -(T₀ ^ 37) * (ηb₀ : CyclotomicField 37 ℚ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  -- §A. The proven integral L2 producer: a specific integral-unit choice of factor data.
  obtain ⟨ηa₀, ηb₀, ρa₀, ρb₀, ua, ub, hηa₀, hηb₀, hua, hub, hfa₀, hfb₀⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo_withUnits D.toRealCaseIIData37 hcop
  have hηOne : (D.etaOne : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger :=
    caseII_etaOne_coe_eq_zeta D.toRealCaseIIData37 hp
  have hηTwo : (D.etaTwo : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger ^ 2 := by
    rw [caseII_etaTwo_coe_eq_zeta_sq D.toRealCaseIIData37 hp]
    exact (pow_two _).symm
  -- Integral generators `r_a, r_b` (`ρ_a⁰ = algebraMap r_a`, `ρ_b⁰ = algebraMap r_b`).
  obtain ⟨ra, hra⟩ := caseII_factorGenerator_integral_of_unitInt D.toRealCaseIIData37 D.etaOne
    D.toCaseIIData37.etaOne_ne_etaZero ηa₀ ρa₀ ua hua (by rw [hηOne]; exact hfa₀)
  obtain ⟨rb, hrb⟩ := caseII_factorGenerator_integral_of_unitInt D.toRealCaseIIData37 D.etaTwo
    D.toCaseIIData37.etaTwo_ne_etaZero ηb₀ ρb₀ ub hub (by rw [hηTwo]; exact hfb₀)
  -- `𝔭`-coprimality of the generators (sharp non-anchor valuation).
  have hra_p : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ra :=
    caseII_zeta_sub_one_not_dvd_factorGenerator D.toRealCaseIIData37 D.etaOne
      D.toCaseIIData37.etaOne_ne_etaZero ηa₀ ρa₀ ua ra hua hra (by rw [hηOne]; exact hfa₀)
  have hrb_p : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ rb :=
    caseII_zeta_sub_one_not_dvd_factorGenerator D.toRealCaseIIData37 D.etaTwo
      D.toCaseIIData37.etaTwo_ne_etaZero ηb₀ ρb₀ ub rb hub hrb (by rw [hηTwo]; exact hfb₀)
  -- The integral factor equations in `𝓞 K`.
  have hFa_int : D.x + D.hζ.toInteger * D.y =
      (1 - D.hζ.toInteger) * (ua : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37 := by
    apply hinj
    simp only [map_add, map_mul, map_sub, map_one, map_pow, hua, hra]
    exact hfa₀
  have hFb_int : D.x + D.hζ.toInteger ^ 2 * D.y =
      (1 - D.hζ.toInteger ^ 2) * (ub : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37 := by
    apply hinj
    simp only [map_add, map_mul, map_sub, map_one, map_pow, hub, hrb]
    rw [map_pow] at hfb₀
    exact hfb₀
  -- §B. The `(1+ζ)`-unit.
  obtain ⟨εp, hεp⟩ := caseII_washington_one_add_zeta_unit D.hζ
  -- §C. The proven L1 anchor: `x + y = u₀·Λ^e·ρ₀³⁷`, `(ρ₀) = B₀`, `2e = 37m+1`.
  obtain ⟨e, u0, ρ0, _he, _hρ0_real, hρ0_span, _hu0_real, hanchor⟩ :=
    caseII_anchor_real_rho0_genuineUnit D.toRealCaseIIData37 hcop
  have hρ0_p : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ρ0 := by
    have hnot : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({ρ0} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [hρ0_span]
      exact fun hdvd => not_p_div_a_zero hp D.hζ D.equation D.hy D.hz hdvd
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  have hρ0sq_p : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ρ0 ^ 2 :=
    fun h => hρ0_p (D.hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h)
  have hz'_spec : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ρ0 ^ 2) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 2 := map_pow _ _ _
  have h2e : 2 * e = 37 * m + 1 :=
    caseII_anchor_exponent_eq D.toRealCaseIIData37 hp
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) hanchor hz'_spec hρ0sq_p
  have hanchor_int : D.x + D.y = (u0 : 𝓞 (CyclotomicField 37 ℚ)) *
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ e * ρ0 ^ 37 := by
    apply hinj
    rw [hanchor]
    simp only [map_mul, map_sub, map_one, map_pow]
  -- §D. The three-term §9.1 descent instance.
  obtain ⟨ε₃, heq⟩ := caseII_washington_threeTermInstance D.toRealCaseIIData37 ua ub u0 εp
    ra rb ρ0 e hεp hFa_int hFb_int hanchor_int h2e
  -- §E. The PROVEN Corollary-8.15 single-index expansion on this instance.
  have hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) := Sinnott.flt37_not_dvd_hPlus
  obtain ⟨d, α, hexp⟩ := caseII_corollary815_singleIndexExpansion37_proven hV hSO
    D.toCaseIIData37 hra_p hrb_p hρ0_p heq
  -- §F. The Lemma-9.9 local power, and the PROVEN discrete-log collapse: a global `37`-th power.
  have hlp := caseII_washington_factorRatio_localPower hSO D ua ub εp ra rb hεp hFa_int hFb_int
  obtain ⟨ε', hε'⟩ := caseIIThm95_descentUnit_isPow_of_singleIndexExpansion
    ((εp * ua) / (-(εp * ub))) d α hexp hlp
  -- §G. Back to `K`: the `K`-value identity `(algebraMap ε')³⁷·(−(1+ζ)·η_b⁰) = (1+ζ)·η_a⁰`.
  have hdivmul : ((εp * ua) / (-(εp * ub)) : (𝓞 (CyclotomicField 37 ℚ))ˣ) * (-(εp * ub)) =
      εp * ua := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hKval := congrArg (fun z : (𝓞 (CyclotomicField 37 ℚ))ˣ =>
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (z : 𝓞 (CyclotomicField 37 ℚ)))
    hdivmul
  rw [hε'] at hKval
  -- Unfold the unit values in `hKval`.
  have hεpK : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
      (εp : 𝓞 (CyclotomicField 37 ℚ)) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) + 1 := by
    rw [hεp, map_add, map_one]
  simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, map_mul, map_neg, map_pow,
    hua, hub] at hKval
  rw [hεpK] at hKval
  set ζK : CyclotomicField 37 ℚ :=
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) with hζK
  set εK : CyclotomicField 37 ℚ :=
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ε' : 𝓞 (CyclotomicField 37 ℚ))
    with hεK
  -- `ζK + 1 ≠ 0` (it is the image of the unit `εp`).
  have hεpK_ne : ζK + 1 ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (εp : 𝓞 (CyclotomicField 37 ℚ)) = 0 := by rw [hεpK]; exact h0
    rw [map_eq_zero_iff _ hinj] at this
    exact Units.ne_zero εp this
  refine ⟨ηa₀, ηb₀, ρa₀, ρb₀, εK, hfa₀, hfb₀, ?_⟩
  -- `hKey : (algebraMap ε')³⁷·(−((ζK+1)·η_b⁰)) = (ζK+1)·η_a⁰`.
  refine mul_left_cancel₀ hεpK_ne ?_
  linear_combination -hKval

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **Representation comparison (§H).**  Any two unit/generator pairs `(η,ρ)`, `(η₀,ρ₀)` solving the
same factor equation `(1−c)·η·ρ³⁷ = n` with `1 − c ≠ 0` and `n ≠ 0` have **nonzero** generators and
**equal** `37`-th-power values `η·ρ³⁷ = η₀·ρ₀³⁷` (cancelling `1 − c`). -/
private theorem caseII_washington_factorRepresentation_pow_eq
    {K : Type*} [Field K] {c n : K} (hc : (1 : K) - c ≠ 0) (hn : n ≠ 0)
    {η η₀ : Kˣ} {ρ ρ₀ : K}
    (h : (1 - c) * (η : K) * ρ ^ 37 = n) (h₀ : (1 - c) * (η₀ : K) * ρ₀ ^ 37 = n) :
    ρ ≠ 0 ∧ ρ₀ ≠ 0 ∧ (η : K) * ρ ^ 37 = (η₀ : K) * ρ₀ ^ 37 := by
  have hρ : ρ ≠ 0 := by
    rintro rfl
    exact hn (by rw [← h, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero])
  have hρ₀ : ρ₀ ≠ 0 := by
    rintro rfl
    exact hn (by rw [← h₀, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero])
  refine ⟨hρ, hρ₀, mul_left_cancel₀ hc ?_⟩
  linear_combination h - h₀

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)] in
/-- **Real `37`-th root from the factor data (§I–§K).**  Given the producer's ratio
`η_a⁰ = −T₀³⁷·η_b⁰` and the two representation comparisons `η_a·ρ_a³⁷ = η_a⁰·ρ_a⁰³⁷`,
`η_b·ρ_b³⁷ = η_b⁰·ρ_b⁰³⁷` (nonzero generators), the combined root `T = −T₀·(ρ_a⁰ρ_b)/(ρ_aρ_b⁰)`
satisfies `η_a/η_b = T³⁷`; reality of `η_a, η_b` makes it conjugation-fixed, so its real `37`-th
root `v` (`caseII_washington_real_root_of_pow_real`) gives `η_a = v³⁷·η_b` with `v` real. -/
private theorem caseII_washington_realRoot_of_factorRatio
    {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
    {ηa ηb ηa₀ ηb₀ : (CyclotomicField 37 ℚ)ˣ} {ρa ρb ρa₀ ρb₀ T₀ : CyclotomicField 37 ℚ}
    (hρa : ρa ≠ 0) (hρb₀ : ρb₀ ≠ 0)
    (hηa : complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
      (ηa : CyclotomicField 37 ℚ))
    (hηb : complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
      (ηb : CyclotomicField 37 ℚ))
    (hKey : (ηa₀ : CyclotomicField 37 ℚ) = -(T₀ ^ 37) * (ηb₀ : CyclotomicField 37 ℚ))
    (heqa : (ηa : CyclotomicField 37 ℚ) * ρa ^ 37 = (ηa₀ : CyclotomicField 37 ℚ) * ρa₀ ^ 37)
    (heqb : (ηb : CyclotomicField 37 ℚ) * ρb ^ 37 = (ηb₀ : CyclotomicField 37 ℚ) * ρb₀ ^ 37) :
    ∃ v : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
        (v : CyclotomicField 37 ℚ) ∧
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb := by
  -- The combined root `T` and the value identity `η_a = T³⁷·η_b`.
  set T : CyclotomicField 37 ℚ := -T₀ * (ρa₀ * ρb) / (ρa * ρb₀) with hT
  have hηaT : (ηa : CyclotomicField 37 ℚ) = T ^ 37 * (ηb : CyclotomicField 37 ℚ) := by
    rw [hT]
    field_simp
    linear_combination ρb₀ ^ 37 * heqa + (T₀ ^ 37 * ρa₀ ^ 37) * heqb +
      (ρa₀ ^ 37 * ρb₀ ^ 37) * hKey
  have hT_ne : T ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide : (37 : ℕ) ≠ 0), zero_mul] at hηaT
    exact Units.ne_zero ηa hηaT
  -- Reality of `T³⁷ = η_a/η_b`, and the real `37`-th root.
  have hT37 : T ^ 37 = (ηa : CyclotomicField 37 ℚ) / (ηb : CyclotomicField 37 ℚ) := by
    rw [hηaT]; field_simp
  have hreal37 : complexConj (CyclotomicField 37 ℚ) (((Units.mk0 T hT_ne :
      (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) ^ 37) =
      ((Units.mk0 T hT_ne : (CyclotomicField 37 ℚ)ˣ) : CyclotomicField 37 ℚ) ^ 37 := by
    rw [Units.val_mk0, hT37, map_div₀, hηa, hηb]
  obtain ⟨v, hv_real, hv37⟩ :=
    caseII_washington_real_root_of_pow_real hζ (Units.mk0 T hT_ne) hreal37
  refine ⟨v, hv_real, ?_⟩
  -- Conclude `η_a = v³⁷·η_b` (unit equality via values).
  have hv37_val : ((v : CyclotomicField 37 ℚ)) ^ 37 = T ^ 37 := by
    have := congrArg (fun z : (CyclotomicField 37 ℚ)ˣ => (z : CyclotomicField 37 ℚ)) hv37
    simpa [Units.val_pow_eq_pow_val] using this
  ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hv37_val]
  exact hηaT

/-! ## 5. The main theorem: real Assumption II for the §9.1 factor units, over the `ℓ ∣ z` datum -/

/-- **[F1 — REAL ASSUMPTION II, PROVEN]** (axiom-clean, under the carried Kellner input
`NoSecondOrderIrregularPair 37 32`).

For a real `ℓ ∣ z` datum `D : RealCaseIIDvdZData37 m` with coprime Fermat variables, **every**
choice of real factor units `η_a, η_b : Kˣ` and generators `ρ_a, ρ_b : K` satisfying the two §9.1
factor equations at `ζ, ζ²` admits a **real** unit `v : Kˣ` with `η_a = v³⁷·η_b`.

This is the **real-Assumption-II conjunct** of the clean Case-II residual
`CaseIIWashingtonCaseII37` (and exactly the statement `CaseIIWashingtonAssumptionIIReal37`),
discharged by the route-(a) finite-field machinery: the proven integral L2 producer + the
three-term §9.1 reassembly (`caseII_washington_threeTermInstance`) make `−(u_a/u_b)` a genuine
descent unit; the **proven** Corollary-8.15 single-index expansion
(`caseII_corollary815_singleIndexExpansion37_proven`), the Lemma-9.9 local power
(`caseII_washington_factorRatio_localPower`, from the proven real-data Lemma 9.8), and the
**proven** discrete-log collapse (`caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`,
operative core `ind₃₇ E₃₂ ≠ 0`) make it a **global** `37`-th power; and the `ζ^{19j}`-absorption
(`caseII_washington_real_root_of_pow_real`) produces the **real** root. -/
theorem caseII_washington_assumptionII_real_of_dvdZ
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))))
    (ηa ηb : (CyclotomicField 37 ℚ)ˣ) (ρa ρb : CyclotomicField 37 ℚ)
    (hηa : complexConj (CyclotomicField 37 ℚ) (ηa : CyclotomicField 37 ℚ) =
      (ηa : CyclotomicField 37 ℚ))
    (hηb : complexConj (CyclotomicField 37 ℚ) (ηb : CyclotomicField 37 ℚ) =
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
        (ηb : CyclotomicField 37 ℚ) * ρb ^ 37) :
    ∃ v : (CyclotomicField 37 ℚ)ˣ,
      complexConj (CyclotomicField 37 ℚ) (v : CyclotomicField 37 ℚ) =
        (v : CyclotomicField 37 ℚ) ∧
      (ηa : (CyclotomicField 37 ℚ)ˣ) = v ^ 37 * ηb := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hηOne : (D.etaOne : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger :=
    caseII_etaOne_coe_eq_zeta D.toRealCaseIIData37 hp
  have hηTwo : (D.etaTwo : 𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger ^ 2 := by
    rw [caseII_etaTwo_coe_eq_zeta_sq D.toRealCaseIIData37 hp]; exact (pow_two _).symm
  -- §A–§G. Algebraic descent: a normalised integral representation with `η_a⁰ = −T₀³⁷·η_b⁰`.
  obtain ⟨ηa₀, ηb₀, ρa₀, ρb₀, T₀, hfa₀, hfb₀, hKey⟩ :=
    caseII_washington_etaZero_descent hSO D hcop
  -- §H. The two §9.1 numerators are nonzero, so the given and producer representations compare.
  have hnum_a : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y ≠ 0 := by
    have h := caseII_algebraMap_x_add_y_eta_ne_zero D.toRealCaseIIData37 hp D.etaOne
    rw [hηOne] at h
    refine fun h0 => h ?_
    rw [map_add, map_mul]; linear_combination h0
  have hnum_b : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) *
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y ≠ 0 := by
    have h := caseII_algebraMap_x_add_y_eta_ne_zero D.toRealCaseIIData37 hp D.etaTwo
    rw [hηTwo] at h
    refine fun h0 => h ?_
    rw [map_add, map_mul]; linear_combination h0
  have h1ζK_ne : (1 : CyclotomicField 37 ℚ) -
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger) ≠ 0 :=
    fun h0 => D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
      (hinj (by rw [map_one]; linear_combination -h0))
  have h1ζ2K_ne : (1 : CyclotomicField 37 ℚ) -
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.hζ.toInteger ^ 2) ≠ 0 :=
    fun h0 => D.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
      (hinj (by rw [map_one]; linear_combination -h0))
  obtain ⟨hρa_ne, _, heqa⟩ :=
    caseII_washington_factorRepresentation_pow_eq h1ζK_ne hnum_a hfa.symm hfa₀.symm
  obtain ⟨_, hρb₀_ne, heqb⟩ :=
    caseII_washington_factorRepresentation_pow_eq h1ζ2K_ne hnum_b hfb.symm hfb₀.symm
  -- §I–§K. The combined real `37`-th root.
  exact caseII_washington_realRoot_of_factorRatio D.hζ hρa_ne hρb₀_ne hηa hηb hKey heqa heqb

/-- **`CaseIIWashingtonAssumptionIIReal37` is PROVEN** (axiom-clean) from the carried Kellner
input `NoSecondOrderIrregularPair 37 32` alone: the real-Assumption-II conjunct of the clean
Case-II residual `CaseIIWashingtonCaseII37` is no longer open content. -/
theorem caseIIWashingtonAssumptionIIReal37_of_noSecondOrder
    (hSO : NoSecondOrderIrregularPair 37 32) :
    CaseIIWashingtonAssumptionIIReal37 :=
  fun D hcop ηa ηb ρa ρb hηa hηb hfa hfb =>
    caseII_washington_assumptionII_real_of_dvdZ hSO D hcop ηa ηb ρa ρb hηa hηb hfa hfb

/-! ## 6. Bonus: the `ρ₀² ∈ 𝔩` conjunct of the clean residual is ALSO proven (Lemma 9.7 descended)

The clean residual's first `ℓ`-propagation conjunct — `ρ₀² ∈ 𝔩` for the anchor generator — is
**derivable** for every antecedent instance: `x + y ∈ 𝔩` (the proven Lemma 9.8 over real data),
`x + y = (ζ−1)^{2e}·(u₀·w'^e)·ρ₀³⁷` (the anchor with `(Λ) = 𝔭²`), and `𝔩` prime, unramified, with
units outside it, force `ρ₀³⁷ ∈ 𝔩`, hence `ρ₀ ∈ 𝔩` and `ρ₀² ∈ 𝔩`.  This is Washington's
`ℓ ∣ ω + θ ⟹ ℓ ∣ ρ₀` (the descended Lemma 9.7), via the kernel
`caseII_dvd_z_of_factorization`.

The two remaining `ℓ`-propagation conjuncts of `CaseIIWashingtonCaseII37` (`ω ∉ 𝔩`, `θ ∉ 𝔩` for
**every** `(η, ρ)`-representation) are **not** per-instance derivable: they are not invariant
under the real rescaling `η_b ↦ η_b·149⁻³⁷`, `ρ_b ↦ 149·ρ_b` (which preserves the entire
antecedent but puts the integer witness `θ = −149²·r_bσr_b` inside `𝔩`).  Their honest discharge
must be keyed to the producer's integral witnesses (as in
`CaseIISection91PContentExtractionDataWithUnits37`), not quantified over all representations. -/

/-- **The `ρ₀² ∈ 𝔩` conjunct of the clean residual, PROVEN** (axiom-clean, under the carried
Kellner input): for a real `ℓ ∣ z` datum and any anchor data `(e, u₀, ρ₀)` with the §9.1 anchor
equation, the anchor generator satisfies `ρ₀² ∈ lv149` — Washington's descended Lemma 9.7
(`ℓ ∣ ω + θ ⟹ ℓ ∣ ρ₀`). -/
theorem caseII_washington_rho0_sq_mem_lv149_of_dvdZ
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIDvdZData37 m)
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
  -- The integral anchor equation.
  have hanchor_int : D.x + D.y = (u0 : 𝓞 (CyclotomicField 37 ℚ)) *
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ e * ρ0 ^ 37 := by
    apply hinj
    rw [hanchor]
    simp only [map_mul, map_sub, map_one, map_pow]
  -- `Λ = (ζ−1)²·w'` for a unit `w'`.
  have hspan := caseII_span_lambda_eq_p_sq D.hζ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ))
  rw [Ideal.span_singleton_pow] at hspan
  obtain ⟨w', hw'⟩ : Associated ((D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2)
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan.symm
  -- The factorized form `x + y = (ζ−1)^{2e}·(u₀·w'^e)·ρ₀³⁷`.
  have hfact : D.x + D.y = (D.hζ.toInteger - 1) ^ (2 * e) *
      ((u0 * w' ^ e : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) * ρ0 ^ 37 := by
    rw [hanchor_int, ← hw']
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [mul_pow, ← pow_mul]
    ring
  -- Lemma 9.8 over real data (proven): `x + y ∈ 𝔩`; the kernel gives `ρ₀³⁷ ∈ 𝔩`.
  have hsum : D.x + D.y ∈ lv149 :=
    caseII_real_x_add_y_mem_of_dvd_z hSO D.toRealCaseIIData37 D.z_mem D.x_notMem D.y_notMem
  have hρ37 : ρ0 ^ 37 ∈ lv149 := caseII_dvd_z_of_factorization D.hζ hfact hsum
  have hρ : ρ0 ∈ lv149 := Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› 37 hρ37
  rw [pow_two]
  exact Ideal.mul_mem_left _ _ hρ

/-! ## 7. The with-units extraction data PROVEN: the clean Case-II residual is fully retired

Combining **F1** (this file: real Assumption II, `caseII_washington_assumptionII_real_of_dvdZ`)
with **F2** (`CaseIIWashingtonEllPropagation.lean`: the `ℓ`-propagation triple,
`caseII_dvdZ_ellPropagation_withUnits`) discharges the **entire** clean-residual input of the
with-units `p`-content extraction data: `CaseIISection91PContentExtractionDataWithUnits37` is now
**proven** from the carried Kellner input alone.  The proof replays
`caseIISection91PContentExtractionDataWithUnits37_of_caseII` (`CaseIIWashingtonCaseIIClean.lean`)
with the clean-residual invocation replaced by F1 + F2 — sound here because the with-units
antecedent supplies the integral witnesses `u_a, u_b` that the `ℓ`-propagation needs (the bare
`CaseIIWashingtonCaseII37` shape is *not* derivable: see §6).

Consequently the FLT37 Case-II endpoint no longer carries any clean-residual hypothesis: Fermat's
Last Theorem for `37` follows from the threaded **coprimality**, Washington **Lemma 9.6**
(`ℓ ∤ xy` at the rational seed), and the carried **Kellner** input only. -/

set_option maxHeartbeats 1600000 in
-- The bumped `maxHeartbeats` is needed because `intro` must unfold the very large
-- `CaseIISection91PContentExtractionDataWithUnits37` def (a long `∀`/`→`/`∃` chain over the §9.1
-- datum) and the final `refine` reassembles the equally large extraction conclusion (24
-- conjuncts); the `whnf` of these big `def … : Prop`s exceeds the default.
/-- **[F1 + F2 — THE WITH-UNITS EXTRACTION DATA, PROVEN]** (axiom-clean, under the carried
Kellner input): `CaseIISection91PContentExtractionDataWithUnits37` holds.  Real Assumption II is
supplied by `caseII_washington_assumptionII_real_of_dvdZ` (F1, this file) and the aux-prime
`ℓ`-propagation by `caseII_dvdZ_ellPropagation_withUnits` (F2); everything else — the integer
witnesses, the σ-fixed unit `δ'`, the descended Fermat equation, the sharp `𝔭`-invariants, the
anchor-support, and the `p`-content condition — is derived exactly as in
`caseIISection91PContentExtractionDataWithUnits37_of_caseII`. -/
theorem caseIISection91PContentExtractionDataWithUnits37_proven
    (hSO : NoSecondOrderIrregularPair 37 32) :
    CaseIISection91PContentExtractionDataWithUnits37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D hcop ηa ηb ρa ρb ua ub hηa hηb hua hub hfa hfb
  have hp : (37 : ℕ) ≠ 2 := by decide
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  -- L1 (genuine integral unit): the anchor, `(ρ₀) = B₀`, `u₀` real.
  obtain ⟨e, u0, ρ0, he, hρ0_real, hρ0_span, hu0_real, hanchor⟩ :=
    caseII_anchor_real_rho0_genuineUnit D.toRealCaseIIData37 hcop
  -- F1 (PROVEN real Assumption II): the real unit `v` with `η_a = v³⁷·η_b`.
  obtain ⟨v, hv_real, hII⟩ :=
    caseII_washington_assumptionII_real_of_dvdZ hSO D hcop ηa ηb ρa ρb hηa hηb hfa hfb
  -- F2 (PROVEN `ℓ`-propagation): `ρ₀² ∈ 𝔩`, `ω ∉ 𝔩`, `θ ∉ 𝔩`, keyed to this `v` via `u_a, u_b`.
  obtain ⟨hz'_mem, hω_notMem_cond, hθ_notMem_cond⟩ :=
    caseII_dvdZ_ellPropagation_withUnits D hSO ηa ηb v ρa ρb ua ub hua hub hII hfa hfb
      e u0 ρ0 hanchor
  -- The integer descended equation: ω, θ, δ', reality, equation (from u_a, u_b, v integral).
  have hbig : CaseIIIntDescOutput37 D.toRealCaseIIData37 e ρ0 v ρa ρb :=
    caseII_integer_descended_equation_of_unitInt D.toRealCaseIIData37 e he u0 ρ0 hanchor ηa ηb v
      ρa ρb ua ub hua hub hηa hηb hfa hfb hv_real hII
  rw [CaseIIIntDescOutput37] at hbig
  obtain ⟨ω, θ, δ', hω, hθ, hω_real, hθ_real, hint_eq⟩ := hbig
  -- `(ζ−1) ∤ ρ₀²` from `(ρ₀) = B₀` (`𝔭`-coprime anchor), in `D.hζ`- and `zeta_spec`-terms.
  have hz'_cop_dζ : ¬ (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ρ0 ^ 2 := by
    have hnot : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({ρ0 ^ 2} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [← Ideal.span_singleton_pow, hρ0_span]
      intro hdvd
      exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz
        ((Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  have hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ ρ0 ^ 2 := by
    have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec D.toRealCaseIIData37
    intro hdvd; exact hz'_cop_dζ ((hassoc.dvd_iff_dvd_left).mpr hdvd)
  -- `(ζ−1) ∤ θ` (conjugate-norm block `𝔭`-coprime).
  obtain ⟨rb, hrb⟩ := caseII_factorGenerator_integral_of_unitInt D.toRealCaseIIData37
    ⟨D.hζ.toInteger ^ 2, (mem_nthRootsFinset (by norm_num) _).mpr (by
      rw [← pow_mul, mul_comm, pow_mul, D.hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow])⟩ (by
      intro h
      have h2 : (D.hζ.toInteger ^ 2 : 𝓞 (CyclotomicField 37 ℚ)) =
          (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) := by
        have := Subtype.ext_iff.mp h; exact this
      rw [caseII_etaZero_eq_one D.toRealCaseIIData37 hp] at h2
      exact D.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
        h2)
    ηb ρb ub hub (by
      rw [show ((⟨D.hζ.toInteger ^ 2, _⟩ :
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
          𝓞 (CyclotomicField 37 ℚ)) = D.hζ.toInteger ^ 2 from rfl]; exact hfb)
  have hθ_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ :=
    caseII_zeta_sub_one_not_dvd_theta D.toRealCaseIIData37 ηb ρb ub rb θ hub hrb hθ hfb
  -- `algebraMap (ρ₀²) = (algebraMap ρ₀)²` (the `z'`-spec; `z' = ρ₀²` integer).
  have hz'_spec : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ρ0 ^ 2) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 2 := map_pow _ _ _
  -- The anchor-exponent identity `2e = 37m+1`, and the sharp invariants `hxy'`, `hdenom'`.
  have h2e : 2 * e = 37 * m + 1 :=
    caseII_anchor_exponent_eq D.toRealCaseIIData37 hp
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) hanchor hz'_spec hz'_cop_dζ
  obtain ⟨hxy', hdenom'⟩ :=
    caseII_descended_hxy_hdenom (m := m) (D.toCaseIIData37.one_le_m) h2e hint_eq hω_real hθ_real
      hθ_cop hz'_cop
  -- The anchor-support `(z') = 𝔞₀²` (`k = 2`).
  have hz'_span2 : Ideal.span ({ρ0 ^ 2} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ 2 := by
    rw [← Ideal.span_singleton_pow, hρ0_span]
  -- The `p`-content-of-output condition `2·(2e−1) = 37·((2m−1)+1)`.
  have hcontent : ∃ m'' : ℕ, 2 * (2 * e - 1) = 37 * (m'' + 1) := by
    refine ⟨2 * m - 1, ?_⟩
    have hcon := caseII_descended_content_eq D.toRealCaseIIData37 hp
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) hanchor hz'_spec hz'_cop_dζ
    rw [hcon]; have := D.toCaseIIData37.one_le_m; congr 1; omega
  -- `η₀ = algebraMap u₀` as a `Kˣ`-unit, ρ₀ promoted to `K`, and the `δ'`-clause derivation.
  refine ⟨e, 2, (IsUnit.map (algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ)).toMonoidHom u0.isUnit).unit, v,
    algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0, ω, θ, ρ0 ^ 2, δ',
    he, by norm_num, ?_, hII, ?_, hω, hθ, hz'_spec, ?_, hω_real, hθ_real, hθ_cop,
    hxy', hdenom', hz'_span2, hint_eq, hz'_mem, hω_notMem_cond ω hω, hθ_notMem_cond θ hθ,
    hcontent⟩
  · -- anchor equation with `η₀ = algebraMap u₀`, ρ₀ = algebraMap ρ₀.
    rw [IsUnit.unit_spec]; exact hanchor
  · -- reality of `η₀ = algebraMap u₀`.
    rw [IsUnit.unit_spec]
    change complexConj (CyclotomicField 37 ℚ)
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _)) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u0 : 𝓞 _)
    rw [← coe_ringOfIntegersComplexConj (K := CyclotomicField 37 ℚ), hu0_real]
  · -- the `δ'`-clause (the σ-fixed-unit characterisation), via injectivity + cancellation.
    intro δ _ hδ_eq
    have hLHS : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (ω ^ 37 + θ ^ 37) =
        ((v : CyclotomicField 37 ℚ) ^ 2 * (ρa * complexConj (CyclotomicField 37 ℚ) ρa)) ^ 37 +
          (-(ρb * complexConj (CyclotomicField 37 ℚ) ρb)) ^ 37 := by
      rw [map_add, map_pow, map_pow, hω, hθ]
    have hRHS := congrArg (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) hint_eq
    rw [hLHS, map_mul, map_mul, map_pow, map_pow] at hRHS
    have hΛ_ne : (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
          (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ (2 * e - 1) ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, map_eq_zero_iff _ hinj]
      refine mul_ne_zero (sub_ne_zero.mpr fun h => ?_) (sub_ne_zero.mpr fun h => ?_)
      · exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one
          (by decide : 1 < 37) h.symm
      · have hp37 : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 37 = 1 :=
          (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one
        have heq : (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 37 =
            (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 *
              (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger := by rw [← pow_succ]
        rw [hp37, ← h, one_mul] at heq
        exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one
          (by decide : 1 < 37) heq.symm
    have hX_ne : ((algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0) ^ 2) ^ 37
        ≠ 0 := by
      refine pow_ne_zero _ (pow_ne_zero _ ?_)
      rw [Ne, map_eq_zero_iff _ hinj]
      intro h0
      refine caseII_data_x_add_y_ne_zero D.toRealCaseIIData37 (by decide : (37 : ℕ) ≠ 2) ?_
      apply hinj
      rw [map_zero, hanchor, h0, map_zero, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero]
    have hcancel := hδ_eq.symm.trans hRHS
    exact mul_right_cancel₀ hΛ_ne (mul_right_cancel₀ hX_ne hcancel)

/-- **[F1 + F2 — FLT37 WITH THE CLEAN CASE-II RESIDUAL RETIRED]** Fermat's Last Theorem for `37`,
with **no** clean-residual hypothesis: from the threaded per-datum **coprimality**, Washington
**Lemma 9.6** (`ℓ ∤ xy` at the rational seed), and the carried **Kellner** input
(`NoSecondOrderIrregularPair 37 32`) alone.

Real Assumption II (F1) and the aux-prime `ℓ`-propagation (F2) are **proven**, so the with-units
`p`-content extraction data is proven (`caseIISection91PContentExtractionDataWithUnits37_proven`)
and the Case-II bridge follows by the existing clean chain
(`caseIIBridge_thirtyseven_of_caseII_withUnits`). -/
theorem fermatLastTheoremFor_thirtyseven_of_lemma96_coprimality
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
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact BernoulliRegular.fermatLastTheoremFor_thirtyseven_of_remaining
    (BernoulliRegular.cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_caseII_withUnits
      (caseIISection91PContentExtractionDataWithUnits37_proven noSecondOrderIrregular)
      h_cop h_lemma96)

end BernoulliRegular.FLT37.Eichler

end

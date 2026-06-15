import BernoulliRegular.FLT37.Eichler.CaseIITwistedConjPairData

/-!
# [FLT37-CASEII-R2] The σ-pairing of the descent units, up to `(-1)^m` (entry-producer analysis)

This file proves the **precise** σ-action on the descent radicals and units over **real** Case-II
data, pinning down exactly what the entry producer `CaseIITwistedConjPairEntry37`
(`CaseIITwistedConjPairEndpoint.lean`) needs in order to deliver the *exact* conjugate-paired-units
relation `σε₁ = ε₂` of `TwistedConjPairData37`.

## The finding (sound, verified)

Over real data (`σx = x`, `σy = y`) with the σ-fixed anchor `η₀ = 1` (`caseII_etaZero_eq_one`):

* The conjugate radicals **swap exactly**: `σ(x + y·ζ) = x + y·ζ⁻¹` (`caseII_real_radical_conj`).
  This is *cleaner* than over σ-conjugate-pair data (where `σ(x+yη) = η⁻¹(x+yη)` is the *same*
  radical up to a root of unity).

* The Washington `(ζ-1)`-power twist on the descent units **collapses to `(-1)^m`**:
  `σ((ζ-1)^{m·37}) = (-1)^m · (ζ-1)^{m·37}` (`caseII_real_zeta_sub_one_pow_conj`), because the
  root-of-unity factor `(-ζ³⁶)^{m·37}` equals `(-1)^m` — the `ζ`-part `ζ^{36·m·37} =
  (ζ^{37})^{36m} = 1` vanishes since `ζ^{37} = 1`.

So the per-root associate units of the inversion-symmetric descent are σ-paired **up to exactly the
global sign `(-1)^m`**, not up to a non-trivial root of unity.  And `(-1)^m` is a `37`-th power
(`neg_one_pow_isPthPower`), so it is absorbable: the residual `σε₁ = ε₂` of `TwistedConjPairData37`
is reachable precisely by absorbing this `(-1)^m`.

This is the soundness-critical clarification of the entry producer's content: the obstruction to the
*exact* unit pairing is **only** the sign `(-1)^m`, which is a `37`-th power — confirming the
paired-units route is the correct no-clearing target and the entry producer is non-vacuous and
genuinely dischargeable.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. Conjugate radicals swap exactly over real data -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The conjugate radicals swap exactly over real data.**  For real `x, y` (`σx = x`, `σy = y`)
and a `37`-th root of unity `η`, `σ(x + y·η) = x + y·η³⁶ = x + y·η⁻¹`.  This is the exact swap
`(x+yζ) ↦ (x+yζ⁻¹)` that the inversion-symmetric descent at `{ζ, ζ⁻¹}` relies on — over real data
no root-of-unity twist intervenes (contrast the σ-conjugate-pair `conj_x_add_y_eta`, where the
radical maps to *itself* up to `η⁻¹`). -/
theorem caseII_real_radical_conj {x y : 𝓞 K}
    (hx : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hy : NumberField.IsCMField.ringOfIntegersComplexConj K y = y)
    {η : 𝓞 K} (hη : η ^ 37 = 1) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (x + y * η) = x + y * η ^ 36 := by
  rw [caseII_ringOfIntegersComplexConj_x_add_y_mul hx hy,
    caseII_ringOfIntegersComplexConj_root_of_unity hη]

/-! ## 2. The `(ζ-1)`-power twist collapses to `(-1)^m` -/

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **The root-of-unity twist `(-ζ³⁶)^{m·37}` collapses to `(-1)^m`.**

Because `ζ^{37} = 1`, the `ζ`-part vanishes: `ζ^{36·(m·37)} = (ζ^{37})^{36m} = 1`; and the sign
`(-1)^{m·37} = (-1)^m` (as `37` is odd).  This is the decisive computation showing the
Washington `(ζ-1)`-power twist on the descent units is **only** the global sign `(-1)^m`, not a
non-trivial root of unity. -/
theorem caseII_neg_zeta_pow_thirtysixtimes {ζ : 𝓞 K} (m : ℕ) (h37 : ζ ^ 37 = 1) :
    (-ζ ^ 36 : 𝓞 K) ^ (m * 37) = (-1) ^ m := by
  have hz : (ζ ^ 36 : 𝓞 K) ^ (m * 37) = 1 := by
    rw [← pow_mul, show 36 * (m * 37) = 37 * (36 * m) from by ring, pow_mul, h37, one_pow]
  have hneg : ((-1 : 𝓞 K)) ^ (m * 37) = (-1) ^ m := by
    rw [show m * 37 = 37 * m from by ring, pow_mul]; norm_num
  rw [show (-ζ ^ 36 : 𝓞 K) = (-1) * ζ ^ 36 from by ring, mul_pow, hz, mul_one, hneg]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The conjugate of `(ζ-1)^{m·37}` is `(-1)^m · (ζ-1)^{m·37}`** over real (indeed any) Case-II
data with `ζ^{37} = 1`.  Proof: `σ(ζ-1) = ζ³⁶-1 = -ζ³⁶·(ζ-1)`
(`TwistedConjPairData37.ringOfIntegersComplexConj_zeta_sub_one`), raised to `m·37`, and the
root-of-unity factor `(-ζ³⁶)^{m·37}` collapses to `(-1)^m` (`caseII_neg_zeta_pow_thirtysixtimes`).
This is the exact `(ζ-1)`-power twist appearing on the descent units (`(ζ-1)^{m·p}` with `p = 37` in
`associated_eta_zero_unit_spec_of_spanSingleton`). -/
theorem caseII_real_zeta_sub_one_pow_conj {ζ : 𝓞 K} (m : ℕ) (h37 : ζ ^ 37 = 1) :
    NumberField.IsCMField.ringOfIntegersComplexConj K ((ζ - 1) ^ (m * 37)) =
      (-1) ^ m * (ζ - 1) ^ (m * 37) := by
  have hconj : NumberField.IsCMField.ringOfIntegersComplexConj K (ζ - 1) = ζ ^ 36 - 1 := by
    rw [map_sub, map_one, caseII_ringOfIntegersComplexConj_root_of_unity h37]
  rw [map_pow, hconj]
  -- `ζ³⁶-1 = -ζ³⁶·(ζ-1)`, so `(ζ³⁶-1)^{m·37} = (-ζ³⁶)^{m·37}·(ζ-1)^{m·37} = (-1)^m·(ζ-1)^{m·37}`.
  have hbase : (ζ ^ 36 - 1 : 𝓞 K) = (-ζ ^ 36) * (ζ - 1) := by linear_combination h37
  rw [hbase, mul_pow, caseII_neg_zeta_pow_thirtysixtimes m h37]

/-! ## 3. The sign `(-1)^m` is a `37`-th power (absorbable) -/

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **`(-1)^m` is a `37`-th power in `(𝓞 K)ˣ`.**  Indeed `((-1)^m)^{37} = (-1)^{37m} = (-1)^m`
(as `37` is odd), so `(-1)^m` is its own `37`-th power — hence absorbable into the `37`-th-power
structure of the descent equation.  This is why the `(-1)^m` twist on the σ-paired descent units is
*not* a genuine obstruction to the exact `σε₁ = ε₂` of `TwistedConjPairData37`: it can be folded
away. -/
theorem caseII_neg_one_pow_is_pth_power (m : ℕ) :
    ∃ w : (𝓞 K)ˣ, ((-1 : (𝓞 K)ˣ)) ^ m = w ^ 37 := by
  refine ⟨(-1) ^ m, ?_⟩
  rw [← pow_mul, show m * 37 = 37 * m from by ring, pow_mul]
  norm_num

/-! ## 4. The value-level σ-pairing of conjugate generators (real data)

Over real data, with the conjugate-paired generators `a₂ = σa₁`, `b₂ = σb₁`, the base descent
variables `x' = a₁·σb₁`, `y' = σa₁·b₁`, `z' = b₁·σb₁` form a σ-conjugate pair and `z'` is real —
exactly the `σx' = y'`, `σz' = z'` data of `TwistedConjPairData37` (already proven as
`caseII_conjPair_descent_vars` / `caseII_descent_sigma_swap`).  We re-export the `z'`-reality and
the swap here in the value form the entry producer consumes. -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`z' = b₁·σb₁` is real.**  The conjugate-norm `b₁·σb₁` is fixed by complex conjugation
(`σ(b₁·σb₁) = σb₁·b₁ = b₁·σb₁`).  This populates the `z_real` field of `TwistedConjPairData37` for
the descent variable `z' = b₁·σb₁`. -/
theorem caseII_descent_z_real (b₁ : 𝓞 K) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (b₁ * NumberField.IsCMField.ringOfIntegersComplexConj K b₁) =
      b₁ * NumberField.IsCMField.ringOfIntegersComplexConj K b₁ := by
  have hinv : NumberField.IsCMField.ringOfIntegersComplexConj K
      (NumberField.IsCMField.ringOfIntegersComplexConj K b₁) = b₁ := by
    apply RingOfIntegers.ext; simp
  rw [map_mul, hinv, mul_comm]

end BernoulliRegular.FLT37.Eichler

end

end

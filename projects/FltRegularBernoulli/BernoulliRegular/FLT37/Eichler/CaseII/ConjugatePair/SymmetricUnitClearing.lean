import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.ThreeTermDescentEquation

/-!
# [FLT37-CASEII-R2] The descent unit `ε₁` is a `37`-th power — the symmetric clearing

This file implements the **ε₁-is-a-37th-power** resolution of the σ-conjugate-pair unit-clearing
step `CaseIIConjPairUnitClearingStep37` (`CaseIIConjPairThreeTermDescent.lean`, §4) — the
heart R2 of the FLT37 Case-II descent.

## The resolution

The proved σ-conjugate-pair 6-unit descent equation
(`ConjPairCaseIIData37.exists_sixUnit_descent_equation`) reads
`ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`.  Prior endpoints blocked on the
*single-unit clearing*: the existing reduction absorbs `ε' = (ε₁/ε₂)^{1/37}` into
`x'`, which is **not** σ-symmetric and breaks the σ-conjugate pair.  The resolution
is the **symmetric clearing**:

* if `ε₁ = δ₁^37` is a `37`-th power, set `x'' = δ₁·x'`, `y'' = σ(δ₁)·y'`,
  `z'' = z'`, `ε'' = ε₃`.  Then, **provided** `σx' = y'` and `σε₁ = ε₂`, we get
  `σx'' = σ(δ₁)·y' = y''` (the σ-conjugate pair is preserved) and
  `x''^37 + y''^37 = δ₁^37·x'^37 + σ(δ₁)^37·y'^37 = ε₁·x'^37 + σ(ε₁)·y'^37`
  `= ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37` (the clean equation).

  No `δ`-σ-obstruction: the **same** `δ₁` and its conjugate `σ(δ₁)` clear `ε₁` and
  `ε₂ = σ(ε₁)` *symmetrically*.

This file proves the two **fully-algebraic cores** of the resolution:

* §1 — `unit_isPow_of_prod_isPow_of_quotient_isPow` — **the `ε₁`-`37`-th-power
  combination**: if `ε₁·σ(ε₁)` (the `K/K⁺` norm) and `ε₁/σ(ε₁)` are both `37`-th
  powers, then `ε₁` is a `37`-th power.  Pure unit arithmetic using
  `2·19 ≡ 1 (mod 37)`: `ε₁² = (ε₁σε₁)·(ε₁/σε₁)` is a `37`-th power, and
  `ε₁ = (ε₁²)^{19}·(ε₁⁻¹)^{37}`.

* §2 — `caseII_conjPair_symmetric_clear` — **the symmetric clearing**: given
  `σx' = y'`, `σε₁ = ε₂`, `ε₁ = δ₁^37`, and the 6-unit descent equation, it produces
  the clean σ-conjugate-pair solution (`σx'' = y''`, `σy'' = x''`,
  `(ζ-1) ∤ y'', z''`, `x''^37 + y''^37 = ε₃·((ζ-1)^m·z'')^37`) — exactly the
  conclusion of `CaseIIConjPairUnitClearingStep37`.  This dissolves the documented
  δ-σ-obstruction.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent, Lemma 9.2), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The `ε₁`-is-a-`37`-th-power combination (pure unit arithmetic)

If both the `K/K⁺` norm `ε₁·σ(ε₁)` (a real unit) and the anti-real ratio
`ε₁/σ(ε₁)` are `37`-th powers, then `ε₁` is a `37`-th power.  This is the elementary
group-theoretic combination: `ε₁² = (ε₁σε₁)·(ε₁/σε₁)`, so `ε₁²` is a `37`-th power,
say `ε₁² = w^37`; then since `2·19 = 38 ≡ 1 (mod 37)`,

  `ε₁ = ε₁^{38}·ε₁^{-37} = (ε₁²)^{19}·(ε₁⁻¹)^{37} = (w^{19}·ε₁⁻¹)^{37}`.

Stated abstractly in any commutative group; the caller supplies `ε₁·σε₁` and
`ε₁/σε₁`. -/

/-- **`ε₁` is a `37`-th power from the norm and anti-ratio being `37`-th powers.**

Abstract commutative-group form: for units `a b` of `𝓞 K`, if the product `a * b`
and the quotient `a / b` are both `37`-th powers, then `a` is a `37`-th power.
Reason: `a² = (a*b)·(a/b)` is a `37`-th power `w^37`, and `2·19 ≡ 1 (mod 37)` gives
`a = (a²)^{19}·(a⁻¹)^{37} = (w^{19}·a⁻¹)^{37}`.

Applied with `a = ε₁`, `b = σ(ε₁)`: `a*b = ε₁σε₁` (the real norm, a `37`-th power by
Kummer's lemma for the plus part) and `a/b = ε₁/σε₁` (a `37`-th power by Assumption
II once `σε₁` is identified with `ε₂`). -/
theorem unit_isPow_of_prod_isPow_of_quotient_isPow
    {K : Type} [Field K] [NumberField K]
    {a b : (𝓞 K)ˣ}
    (hprod : ∃ w : (𝓞 K)ˣ, a * b = w ^ 37)
    (hquot : ∃ v : (𝓞 K)ˣ, a / b = v ^ 37) :
    ∃ δ : (𝓞 K)ˣ, a = δ ^ 37 := by
  obtain ⟨w, hw⟩ := hprod
  obtain ⟨v, hv⟩ := hquot
  -- `a² = (a*b)·(a/b) = w^37 · v^37 = (w·v)^37`.
  have hsq : a ^ 2 = (w * v) ^ 37 := by
    rw [mul_pow, ← hw, ← hv, sq, div_eq_mul_inv]
    -- `a * a = (a * b) * (a * b⁻¹)`: expand RHS to `a·b·a·b⁻¹ = a·a`.
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
  -- `a = ((w·v)^{19}·a⁻¹)^{37}`: the RHS is `((w·v)^{37})^{19}·a^{-37}`
  -- `= (a²)^{19}·a^{-37} = a^{38}·a^{-37} = a` (using `2·19 = 38 = 37 + 1`).
  refine ⟨(w * v) ^ 19 * a⁻¹, ?_⟩
  have : ((w * v) ^ 19 * a⁻¹) ^ 37 = ((w * v) ^ 37) ^ 19 * (a ^ 37)⁻¹ := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 19 37, inv_pow]
  rw [this, ← hsq, ← pow_mul, show (2 * 19 : ℕ) = 37 + 1 from by norm_num, pow_add, pow_one,
    mul_right_comm, mul_inv_cancel, one_mul]

/-! ## 2. The symmetric clearing (dissolving the δ-σ-obstruction)

Given that `ε₁ = δ₁^37` is a `37`-th power, the substitution `x'' = δ₁·x'`,
`y'' = σ(δ₁)·y'`, `z'' = z'`, `ε'' = ε₃` clears the two leading units `ε₁, ε₂` into
the clean σ-conjugate-pair shape — **provided** the descent variables form a
σ-conjugate pair (`σx' = y'`) and the descent units are σ-conjugate (`σε₁ = ε₂`).
The key cancellations:

* **σ-pair preserved:** `σx'' = σ(δ₁)·σ(x') = σ(δ₁)·y' = y''`, and (`σ² = id`)
  `σy'' = σ(σδ₁)·σ(y') = δ₁·x' = x''`.
* **clean equation:** `x''^37 + y''^37 = δ₁^37·x'^37 + σ(δ₁)^37·y'^37`.  Now
  `δ₁^37 = ε₁` and `σ(δ₁)^37 = σ(δ₁^37) = σ(ε₁) = ε₂`, so this is
  `ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`.

The **same** `δ₁` (clearing `ε₁`) and its conjugate `σ(δ₁)` (clearing `ε₂ = σε₁`)
act symmetrically — there is **no** δ-σ-obstruction (the prior block was caused by
the *asymmetric* absorption of `(ε₁/ε₂)^{1/37}` into `x'` alone, breaking `σx' = y'`).

For the σ-conjugate-pair *conclusion* shape only the divisibility `(ζ-1) ∤ y'', z''`
and the equation are needed (the `of_conjPairSolution` constructor populates
`x_conj`/`y_conj` from `σx'' = y''`, `σy'' = x''`). -/

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The symmetric clearing produces the clean σ-conjugate-pair solution.**

Given:
* a 6-unit descent equation `ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`, `(ζ-1) ∤ y', z'`;
* the **σ-conjugate-pair** structure of the descent variables `σx' = y'`;
* the **σ-conjugate-pairing** of the leading units `σε₁ = ε₂` (as units of `𝓞 K`);
* a `37`-th-root witness `ε₁ = δ₁^37`;

the substitution `x'' = δ₁·x'`, `y'' = σ(δ₁)·y'`, `z'' = z'`, `ε'' = ε₃` gives a clean
σ-conjugate-pair solution: `σx'' = y''`, `σy'' = x''`, `(ζ-1) ∤ y'', z''`, and
`x''^37 + y''^37 = ε₃·((ζ-1)^m·z'')^37`.

This is the conclusion shape of `CaseIIConjPairUnitClearingStep37`, with the δ-σ-obstruction
dissolved. -/
theorem caseII_conjPair_symmetric_clear
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) {m : ℕ}
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ} {δ₁ : (𝓞 K)ˣ}
    (hy' : ¬ (hζ.unit'.1 - 1) ∣ y')
    (hz' : ¬ (hζ.unit'.1 - 1) ∣ z')
    (hx'_conj : ringOfIntegersComplexConj K x' = y')
    (hε_conj : unitsComplexConj K ε₁ = ε₂)
    (hδ : ε₁ = δ₁ ^ 37)
    (heq : (ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
      (ε₃ : 𝓞 K) * ((hζ.unit'.1 - 1) ^ m * z') ^ 37) :
    ∃ (x'' y'' z'' : 𝓞 K) (ε'' : (𝓞 K)ˣ),
      ringOfIntegersComplexConj K x'' = y'' ∧
      ringOfIntegersComplexConj K y'' = x'' ∧
      ¬ (hζ.unit'.1 - 1) ∣ y'' ∧
      ¬ (hζ.unit'.1 - 1) ∣ z'' ∧
      x'' ^ 37 + y'' ^ 37 =
        (ε'' : 𝓞 K) * ((hζ.unit'.1 - 1) ^ m * z'') ^ 37 := by
  classical
  -- `σ δ₁` as an element of `𝓞 K`: the conjugate of the witness unit.
  -- The units-vs-elements bridge `(unitsComplexConj K u : 𝓞 K) = σ (u : 𝓞 K)` is `rfl`.
  have hσ_unit : ∀ u : (𝓞 K)ˣ,
      ringOfIntegersComplexConj K (u : 𝓞 K)
        = ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) := by
    intro _; rfl
  have hσ_invol : ∀ w : 𝓞 K,
      ringOfIntegersComplexConj K (ringOfIntegersComplexConj K w) = w := by
    intro w; apply RingOfIntegers.ext; simp
  -- Define the cleared variables `x'' = δ₁·x'`, `y'' = σ(δ₁)·y'`, `z'' = z'`, `ε'' = ε₃`.
  refine ⟨(δ₁ : 𝓞 K) * x', ringOfIntegersComplexConj K (δ₁ : 𝓞 K) * y', z', ε₃,
    ?_, ?_, ?_, hz', ?_⟩
  · -- `σ(δ₁·x') = σ(δ₁)·σ(x') = σ(δ₁)·y'`.
    rw [map_mul, hx'_conj]
  · -- `σ(σ(δ₁)·y') = σ(σδ₁)·σ(y')`; `σ(σδ₁) = δ₁` and `σ(y') = σ(σx') = x'`.
    rw [map_mul, hσ_invol, show y' = ringOfIntegersComplexConj K x' from hx'_conj.symm, hσ_invol]
  · -- `(ζ-1) ∤ σ(δ₁)·y'`: `σ(δ₁)` is a unit, so reduces to `(ζ-1) ∤ y'`.
    intro hdvd
    apply hy'
    have hunit : IsUnit (ringOfIntegersComplexConj K (δ₁ : 𝓞 K)) := by
      rw [hσ_unit]; exact (unitsComplexConj K δ₁).isUnit
    exact hunit.dvd_mul_left.mp hdvd
  · -- Clean equation `(δ₁·x')^37 + (σδ₁·y')^37 = ε₁x'^37 + ε₂y'^37 = ε₃((ζ-1)^m·z')^37`.
    have hδ_val : ((δ₁ : 𝓞 K)) ^ 37 = (ε₁ : 𝓞 K) := by
      rw [← Units.val_pow_eq_pow_val, ← hδ]
    have hσδ_val : (ringOfIntegersComplexConj K (δ₁ : 𝓞 K)) ^ 37 = (ε₂ : 𝓞 K) := by
      rw [hσ_unit, ← Units.val_pow_eq_pow_val, ← map_pow, ← hδ, hε_conj]
    calc ((δ₁ : 𝓞 K) * x') ^ 37 + (ringOfIntegersComplexConj K (δ₁ : 𝓞 K) * y') ^ 37
        = ((δ₁ : 𝓞 K)) ^ 37 * x' ^ 37 +
            (ringOfIntegersComplexConj K (δ₁ : 𝓞 K)) ^ 37 * y' ^ 37 := by
          rw [mul_pow, mul_pow]
      _ = (ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 := by rw [hδ_val, hσδ_val]
      _ = (ε₃ : 𝓞 K) * ((hζ.unit'.1 - 1) ^ m * z') ^ 37 := heq

end BernoulliRegular.FLT37.Eichler

end

end

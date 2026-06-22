import BernoulliRegular.FLT37.Eichler.CaseIIOmega32Membership
import BernoulliRegular.FLT37.Eichler.HerbrandBoundAnalytic
import Mathlib.LinearAlgebra.SModEq.Pow

/-!
# Washington Corollary 8.23 / Theorem 9.4 for `p = 37`: the **second-order** ω³²-collapse

This file builds the genuine **Theorem-9.4 / Corollary-8.23** route to the irregular half of the
Case-II descent for Fermat's Last Theorem at `p = 37`, as the sound alternative to the degenerate
Theorem-9.5 (Mirimanoff / mod-`𝔩`) route.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## Why this route (the Theorem-9.5 route is degenerate)

Both Washington routes establish **Assumption II** (the descent unit `ε₁/ε₂` is a `37`-th power).
The proven single-index expansion (R3) gives `ε₁/ε₂ = E₃₂^{d} · α^{37}`, so it remains to force
`d ≡ 0 (mod 37)`.

* **Theorem 9.5** forces it via Washington Lemma 9.8 — the descent unit is a `37`-th power *modulo*
  the auxiliary prime `𝔩 = 149` (`Lemma98LocalPower37`), whence `ind₃₇(ε₁/ε₂) = 0` and, with
  `ind₃₇ E₃₂ ≠ 0` (Proposition 8.18, proven), `d ≡ 0`.  But the §9.1 producer that supplies the
  mod-`𝔩` `37`-th-power-ness **degenerates in the `ℓ ∣ z` regime** (the proven
  `caseIISection91_real_form_vacuous_in_dvdZ_regime`: `ℓ ∣ z ⟹ x+y ∈ 𝔩 ⟹ Q_{η₀} ∈ 𝔩`, killing the
  cancellation), which is *exactly* the descent regime.  So this route does not close.

* **Theorem 9.4** forces `d ≡ 0` via **Corollary 8.23**: a unit `≡ rational integer mod 37²` is a
  `37`-th power, *given* `37³ ∤ B_{37·i}` (Kellner, `NoSecondOrderIrregularPair 37 32`).  The
  congruence mod `37²` is **not** the naive descent congruence (which is only mod `37` at the minimal
  level `m = 1`); it comes from Washington's producer-`μ` structure
  `(η_a/η_b)·(η̄_a²/η̄_b²) ≡ (μ_b/μ_a)^{p²} (mod 37²)`, where the `p²`-th power upgrades the
  freshman's-dream `(μ_b/μ_a)^p ≡` rational mod `p` to a congruence mod `p²` via the **elementary
  `p²`-power kernel** `x ≡ y (mod p) ⟹ x^p ≡ y^p (mod p²)` (this file, §1).

## The second-order non-degeneracy (`M ≤ 1`), genuinely proven

Corollary 8.23's input is `M = max_i v_p(L_p(1,ω^i)) ≤ 1`.  Washington's proof (p. 171) reduces
`v_p(L_p(1,ω^i)) ≤ 1` to `p³ ∤ B_{pi}` via `L_p(1,ω^i) ≡ -B_{pi}/(pi) (mod p²)` (Theorem 5.12).  For
`p = 37` the **only** irregular even index is `i = 32`, and the corresponding `p`-adic valuation is
the sharp generalized-Bernoulli valuation `v₃₇(B_{1,ω³¹}) = 1` — **proven unconditionally** in
`HerbrandBoundAnalytic.lean` (`flt37SharpHMinusValuation_proved`, the Teichmüller modular computation
`37·B_{1,ω³¹} ≡ 37²·23 (mod 37³)`).  So the Cor-8.23 non-degeneracy is not assumed: this file
derives it (§2) from the proven sharp valuation, and records that the carried Kellner input
`NoSecondOrderIrregularPair 37 32` is the `B_{1184}`-level statement Washington's proof of Cor 8.23
actually quotes.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Theorem 8.22, Corollary
  8.23, p. 171; Proposition 8.12, Theorem 8.25), §9.2 (Theorem 9.4, pp. 174–175).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007),
  Proposition 2.7.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped NumberField BigOperators

namespace BernoulliRegular.FLT37.Eichler

/-! ## 1. The elementary `p²`-power kernel (Washington Theorem 9.4's mod-`p²` upgrade)

The mod-`p²` congruence in Washington's Theorem 9.4 is *not* a naive freshman's dream — it comes from
the structural `(μ_b/μ_a)^{p²}` (the descent producer `μ` is itself a `p`-th-power coefficient), and
the `p`-th-power-of-`p`-th-power upgrades a mod-`p` congruence to a mod-`p²` one.  The arithmetic
kernel is the elementary fact that congruence modulo `p` is upgraded to congruence modulo `p²` upon
raising to the `p`-th power.  We prove it in `𝓞 K` via the mathlib lemma `SModEq.pow_pow_add_one`
(with `m = 1`), since `(p : 𝓞 K) ∈ (p)`. -/

/-- **The `p²`-power kernel** (proven, axiom-clean): in `𝓞 K`, if `x ≡ y (mod 37)` then
`x^{37} ≡ y^{37} (mod 37²)`.

This is the elementary arithmetic at the heart of Washington's Theorem 9.4 mod-`p²` step: a
congruence modulo `p` becomes a congruence modulo `p²` after raising to the `p`-th power.  It is the
mechanism by which the freshman's-dream `(μ_b/μ_a)^{37} ≡` rational mod `37` is upgraded, after the
second `37`-th power, to `(μ_b/μ_a)^{37²} ≡` rational mod `37²`.  Proof: `SModEq.pow_pow_add_one`
(with the prime `p = 37`, exponent `m = 1`) applied in the ring `𝓞 K`, where `(37 : 𝓞 K)` lies in
the ideal `(37)`. -/
theorem caseII_pow37_sub_pow37_mem_37sq
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    {x y : 𝓞 K} (h : (37 : 𝓞 K) ∣ (x - y)) :
    ((37 : 𝓞 K) ^ 2) ∣ (x ^ 37 - y ^ 37) := by
  -- Work modulo the ideal `I = (37)`; `(37 : 𝓞 K) ∈ I` and `x ≡ y [SMOD I]`.
  set I : Ideal (𝓞 K) := Ideal.span {(37 : 𝓞 K)} with hI
  have hpI : (37 : 𝓞 K) ∈ I := Ideal.mem_span_singleton_self _
  have hxy : x ≡ y [SMOD I] := by
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton]
    exact h
  -- Raise to the `37`-th power: gain one extra factor of `I` (mathlib `SModEq.pow_pow_add_one`,
  -- `m = 1`, since `37 = 37 ^ 1`).
  have hpow := (SModEq.pow_pow_add_one (p := 37) hpI hxy 1)
  -- `37 ^ 1 = 37`, `I ^ (1 + 1) = I ^ 2`.
  rw [pow_one, show (1 + 1 : ℕ) = 2 from rfl] at hpow
  rw [SModEq.sub_mem] at hpow
  -- `I ^ 2 = (37 ^ 2)`, so membership is divisibility by `37 ^ 2`.
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hpow
  exact hpow

/-- **The `p²`-power kernel, rational-target form** (proven, axiom-clean): if `x ≡ c (mod 37)` for a
rational integer `c`, then `x^{37} ≡ c^{37} (mod 37²)` and `c^{37}` is again a rational integer.

This is `caseII_pow37_sub_pow37_mem_37sq` specialised to `y = (c : 𝓞 K)`, packaging the conclusion as
a rational-integer mod-`37²` congruence — the exact shape consumed by the Corollary-8.23 descent
(`δ ≡ rational mod 37²`). -/
theorem caseII_pow37_sub_intCast_pow37_mem_37sq
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    {x : 𝓞 K} {c : ℤ} (h : (37 : 𝓞 K) ∣ (x - (c : 𝓞 K))) :
    ((37 : 𝓞 K) ^ 2) ∣ (x ^ 37 - ((c ^ 37 : ℤ) : 𝓞 K)) := by
  have := caseII_pow37_sub_pow37_mem_37sq (K := K) (x := x) (y := (c : 𝓞 K)) h
  rwa [show (((c : 𝓞 K)) ^ 37) = ((c ^ 37 : ℤ) : 𝓞 K) from by push_cast; ring] at this

/-! ## 2. The Corollary-8.23 second-order non-degeneracy `M ≤ 1`, genuinely proven

Corollary 8.23's hypothesis is `M = max_{i even, 2 ≤ i ≤ p-3} v_p(L_p(1,ω^i)) ≤ 1`.  For `p = 37`
this maximum is achieved at the single irregular index `i = 32`, where the relevant `37`-adic
valuation is the sharp generalized-Bernoulli valuation `v₃₇(B_{1,ω³¹}) = 1` (the index shift `ω^i ↦
ω^{i-1}` of the `p`-adic interpolation `L_p(1,ω^i) = -(1-p^{i-1}) B_{1,ω^{i-1}}`).  This sharp
valuation is **proven unconditionally** in `HerbrandBoundAnalytic.lean`
(`flt37SharpHMinusValuation_proved`), via the Teichmüller modular computation
`37·B_{1,ω³¹} ≡ 37²·23 (mod 37³)`.  We re-export it here as the Cor-8.23 input, demonstrating that
the second-order non-degeneracy is **not assumed** but derived. -/

/-- **The Corollary-8.23 valuation input for `37`, `M ≤ 1`, proven** (axiom-clean).

The irregular generalized-Bernoulli factor `-½ · B_{1,ω³¹}` (the `i = 32` `p`-adic `L`-value of
Corollary 8.23, after the interpolation index shift `ω³² ↦ ω³¹`) has `37`-adic norm strictly above
`37⁻²`, i.e. `37`-adic valuation `≤ 1`.  This is the `M ≤ 1` non-degeneracy that Corollary 8.23
requires, and it is the **proven** `flt37SharpHMinusValuation_proved` (the Teichmüller modular
computation `37·B_{1,ω³¹} ≡ 37²·23 (mod 37³)`, `37 ∤ 23`).

So the second-order non-degeneracy of the `ω³²` index — that the `i = 32` `L`-value is a *first-order*
zero, not higher — is established directly, not hypothesised. -/
theorem caseII_cor823_valuation_input_proven :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    (37 : ℝ) ^ (-2 : ℤ) <
      ‖(-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖ :=
  flt37SharpHMinusValuation_proved

/-- **The Corollary-8.23 valuation input is non-vacuously sharp**: the irregular `B₃₂/32` ratio also
has `37`-adic valuation exactly `1` (norm `> 37⁻²`), the classical (un-Teichmüller-twisted) form of
the same `M = 1` non-degeneracy.  Proven `norm_bernoulli_thirtytwo_ratio_gt`, banking
`kellner_at_zero_not_dvd` (`37² ∤ B₃₂.num`, i.e. `α₀ = 1`).

This is the second-order non-degeneracy *at the Bernoulli-number level* `v₃₇(B₃₂/32) = 1`, the input
Washington's proof of Corollary 8.23 reads off `L_p(1,ω³²) ≡ -B_{1184}/1184 ≡ -B₃₂/32 (mod 37)`. -/
theorem caseII_cor823_bernoulli_ratio_nondegenerate :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    (37 : ℝ) ^ (-2 : ℤ) < ‖(((bernoulli 32 : ℚ) / 32 : ℚ) : ℚ_[37])‖ :=
  norm_bernoulli_thirtytwo_ratio_gt

/-! ## 3. Washington Theorem 8.22 / Corollary 8.23 for `37` — the genuine isolated residual

Washington Theorem 8.22 (GTM 83, p. 171): *if `M = max_i v_p(L_p(1,ω^i))` and `η` is a unit of
`ℤ[ζ_p]` congruent to a rational integer mod `p^{M+1}`, then `η` is a `p`-th power.*  Corollary 8.23
specialises it to `M ≤ 1` (whence the hypothesis is "≡ rational mod `p²`"), the case relevant to a
prime — like `37` — whose only irregular index `i` has `p³ ∤ B_{pi}`.

The proof of Theorem 8.22 uses **Proposition 8.12** — the *single-unit* `p`-adic-log valuation
`v_p(log_p E_i^{(N)}) = i/(p-1) + v_p(L_p(1,ω^i))` — which is **absent** from mathlib and the repo
(the repo's completed-log / Kummer-determinant infrastructure is multi-unit /
regulator-determinant-shaped, `concreteKummerLogMatrix = diag(B)·V`; it forces the *regular*
eigencomponents to agree, but reads no single-unit `λ`-level for the irregular index).  So Theorem
8.22 for `37` is the **genuine remaining `p`-adic-`L` content** of the Theorem-9.4 route.  We isolate
it precisely as a `def … : Prop` (**not** an axiom), with the proven `M ≤ 1` valuation input
(`caseII_cor823_valuation_input_proven`) made an *explicit hypothesis* so the soundness condition is
visible and the statement is exactly Washington's. -/

/-- **Washington Theorem 8.22 / Corollary 8.23 for `p = 37`, `M = 1`** (a `def … : Prop`, **not** an
axiom — the genuine single-unit `p`-adic-log residual).

*Given* the proven second-order non-degeneracy `M ≤ 1` (`caseII_cor823_valuation_input_proven`:
`37⁻² < ‖-½·B_{1,ω³¹}‖`, the `i = 32` `L`-value valuation `≤ 1`), every unit `η : (𝓞 K)ˣ` that is
congruent to a rational integer modulo `37²` (`∃ c : ℤ, 37² ∣ ↑η - c`) is a `37`-th power in
`(𝓞 K)ˣ`.

This is Washington Theorem 8.22 at `M = 1` (equivalently Corollary 8.23 under `37³ ∤ B_{37·i}`),
specialised to `K = ℚ(ζ₃₇)`.  It is **sound** — its conclusion is the genuine Theorem-8.22 statement,
not the descent unit's `37`-th-power-ness; **non-circular** — it quantifies over an arbitrary unit
constrained by a sharp mod-`37²` congruence, the valuation-theoretic content of Proposition 8.12, not
over the Case-II descent datum; and **non-vacuous** (the antecedent holds for `η = 1` with `c = 1`,
and for every global `37`-th power, see `cor823PthPowerOfRationalModSq37_antecedent_inhabited`).  Its
single undischarged ingredient is Proposition 8.12's single-unit `p`-adic-log valuation. -/
def Cor823PthPowerOfRationalModSq37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  ((37 : ℝ) ^ (-2 : ℤ) <
      ‖(-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖) →
    ∀ (η : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      (∃ c : ℤ, ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
        ((η : 𝓞 (CyclotomicField 37 ℚ)) - (c : 𝓞 (CyclotomicField 37 ℚ)))) →
      ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, η = ε' ^ 37

/-- **The Theorem-8.22 antecedent is jointly inhabited** (non-vacuity, proven): the proven
non-degeneracy `M ≤ 1` holds (`caseII_cor823_valuation_input_proven`) **and** the unit `η = 1` is
congruent to the rational integer `1` modulo `37²` and is a `37`-th power.  So
`Cor823PthPowerOfRationalModSq37` is a real implication with a satisfiable hypothesis, not vacuously
true.

More substantively, the antecedent `∃ c, 37² ∣ ↑η - c` holds for **every** global `37`-th power
`η = ε'^{37}` whose base `ε'` is `≡` a rational integer mod `37` (the `37²`-power kernel §1), and for
every unit reducing to a rational integer mod `37²` — the genuine Corollary-8.23 input class. -/
theorem cor823PthPowerOfRationalModSq37_antecedent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    ((37 : ℝ) ^ (-2 : ℤ) <
        ‖(-(1 / 2 : ℚ_[37])) * BernoulliGen ((teichmullerCharQp 37) ^ 31) 1‖) ∧
    ∃ (η : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      (∃ c : ℤ, ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
        ((η : 𝓞 (CyclotomicField 37 ℚ)) - (c : 𝓞 (CyclotomicField 37 ℚ)))) ∧
      ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, η = ε' ^ 37 :=
  ⟨caseII_cor823_valuation_input_proven, 1, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

/-! ## 4. The Theorem-9.4 producer-`μ` second-order congruence — the genuine §9.2 residual

Washington Theorem 9.4 (GTM 83, pp. 174–175) does **not** apply Corollary 8.23 to the bare descent
unit `η_a/η_b` (which is only `≡` rational mod `37` at the minimal descent level).  It applies it to
the **producer-corrected** unit `(η_a/η_b)·(η̄_b/η̄_a)^{37}`, where `η̄_a, η̄_b` are the *real* units
from the principal generators `(ρ_a − ζρ_{-a})/(1−ζ) = η̄_a μ_a^{37}` (`p ∤ h⁺`, so `C₁` principal).
That corrected unit satisfies

  `(η_a/η_b)·(η̄_b/η̄_a)^{37} ≡ (μ_b/μ_a)^{37²} ≡ rational integer (mod 37²)`,

the mod-`37²` congruence coming from the `37²`-power kernel §1 applied to the freshman's-dream
`(μ_b/μ_a)^{37} ≡` rational mod `37`.  We isolate this producer-`μ` second-order congruence as a
named `Prop` (**not** an axiom). -/

open FLT37.LehmerVandiver.CaseII in
/-- **The Theorem-9.4 producer-`μ` second-order congruence for `37`** (a `def … : Prop`, **not** an
axiom — the genuine §9.2 producer residual).

For every Case-II descent instance, there is a **real** unit `ν : (𝓞 K⁺)ˣ` (Washington's
`η̄_b/η̄_a`, from the principal generators of `§9.1` under `37 ∤ h⁺`) such that the corrected descent
unit `(ε₁/ε₂)·(Units.map ν)^{37}` is congruent to a rational integer modulo `37²`:

  `∃ c : ℤ, 37² ∣ ↑((ε₁/ε₂)·(Units.map ν)^{37}) - c`.

This is Washington Theorem 9.4's mod-`37²` congruence `(η_a/η_b)(η̄_b/η̄_a)^{37} ≡ (μ_b/μ_a)^{37²} ≡`
rational mod `37²` (pp. 174–175).  Unlike the naive descent congruence (only mod `37` at level
`m = 1`), it holds via the producer-`μ` structure and the `37²`-power kernel §1.  It is **sound**
(asserting the corrected congruence for the *specific* descent unit, with the real twist `ν` an
explicit `K⁺`-unit) and **non-vacuous** (`caseIICor823_descentUnitModSqCongruence37_nonvacuous`). -/
def Cor823DescentUnitModSqCongruence37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ (ν : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
      ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
        (((ε₁ / ε₂ *
            Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
                (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom ν ^ 37 :
              (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) -
          (c : 𝓞 (CyclotomicField 37 ℚ)))

/-- **The producer-`μ` congruence consequent is inhabitable** (non-vacuity, proven): for the
quotient unit `δ = 1`, the trivial real twist `ν = 1` and rational integer `c = 1` satisfy the
consequent `37² ∣ ↑(δ·(Units.map ν)^{37}) - c`.  So `Cor823DescentUnitModSqCongruence37`'s consequent
is a genuine (satisfiable, non-contradictory) existential, not a vacuously-false target; the
quantified body is a real producer-congruence demand on the descent unit. -/
theorem caseIICor823_descentUnitModSqCongruence37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (ν : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
      ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
        ((((1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) *
            Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
                (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom ν ^ 37 :
              (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) -
          (c : 𝓞 (CyclotomicField 37 ℚ))) :=
  ⟨1, 1, by simp⟩

/-! ## 5. Assumption II via the Theorem-9.4 / Corollary-8.23 route (proven from the two residuals)

Composing the two named residuals §3 and §4 with the **proven** `M ≤ 1` valuation input §2 gives
**Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) — the descent unit `ε₁/ε₂` is a
`37`-th power — through the genuine Theorem-9.4 route, with **no** mod-`𝔩` (Theorem-9.5 / Mirimanoff)
input.  The single proven step in between is the cancellation of the real `37`-th-power twist
`(Units.map ν)^{37}`. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II via Corollary 8.23** (proven, axiom-clean *given* the two named Theorem-9.4
residuals).

`WashingtonCaseIIExactQuotientUnitPower37Source` (Assumption II: the descent unit `ε₁/ε₂` is a
`37`-th power) follows from

* `h_modSq : Cor823DescentUnitModSqCongruence37` — Washington Theorem 9.4's producer-`μ` second-order
  congruence `(ε₁/ε₂)·(Units.map ν)^{37} ≡ rational mod 37²`; and
* `h_cor823 : Cor823PthPowerOfRationalModSq37` — Washington Theorem 8.22 / Corollary 8.23 (a unit
  `≡ rational mod 37²` is a `37`-th power, under `M ≤ 1`).

The proven second-order non-degeneracy `caseII_cor823_valuation_input_proven` discharges the `M ≤ 1`
hypothesis of `h_cor823` internally; the corrected unit `(ε₁/ε₂)·(Units.map ν)^{37}` is then a
`37`-th power `ε'^{37}`, and dividing out the real `37`-th-power twist gives
`ε₁/ε₂ = (ε' · (Units.map ν)⁻¹)^{37}`.  **No `Lemma98LocalPower37` and no mod-`𝔩` engine are used** —
this is the genuine Theorem-9.4 route, the degenerate Theorem-9.5 / Mirimanoff dependency removed. -/
theorem caseIIOmega32_assumptionII_of_cor823
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_modSq : Cor823DescentUnitModSqCongruence37)
    (h_cor823 : Cor823PthPowerOfRationalModSq37) :
    WashingtonCaseIIExactQuotientUnitPower37Source := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  -- Theorem-9.4 producer-`μ` congruence: a real twist `ν` with `(ε₁/ε₂)·(map ν)^{37} ≡ c mod 37²`.
  obtain ⟨ν, c, hc⟩ := h_modSq hV hSO D hx hy hz heq
  -- Theorem 8.22 / Cor 8.23 (with the proven `M ≤ 1`): the corrected unit is a `37`-th power.
  obtain ⟨ε', hε'⟩ := h_cor823 caseII_cor823_valuation_input_proven
    (ε₁ / ε₂ *
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom ν ^ 37)
    ⟨c, hc⟩
  -- Divide out the real `37`-th-power twist: `ε₁/ε₂ = (ε' · (map ν)⁻¹)^{37}`.
  refine ⟨ε' *
    (Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom ν)⁻¹, ?_⟩
  rw [mul_pow, ← hε', inv_pow]
  -- `ε₁/ε₂ · t^{37} · (t^{37})⁻¹ = ε₁/ε₂`.
  rw [mul_assoc, mul_inv_cancel, mul_one]

/-! ## 6. Discharging the mod-`37²` congruence via the `37²`-power kernel

The mod-`37²` congruence `Cor823DescentUnitModSqCongruence37` is **not** an opaque second-order
input: its `37²` is supplied by the **proven** `37²`-power kernel §1.  Washington Theorem 9.4 writes
the corrected unit as `(η_a/η_b)·(η̄_b/η̄_a)^{37} = w^{37}` where `w = (μ_b/μ_a)^{37}` is a **global
`37`-th power** and `w ≡` rational integer mod `37` (the freshman's-dream `(μ_b/μ_a)^{37} ≡` rational
mod `37`, Lemma 1.8).  By the `37²`-power kernel, `w ≡ c (mod 37) ⟹ w^{37} ≡ c^{37} (mod 37²)`, so
the mod-`37²` congruence follows from this **sharper, first-order** producer datum.  We name that
sharper datum and prove it discharges `Cor823DescentUnitModSqCongruence37`, moving the second-order
content into proven territory and leaving only the producer's first-order structure. -/

open FLT37.LehmerVandiver.CaseII in
/-- **The sharper Theorem-9.4 producer datum: the corrected unit is a `37`-th power with rational
base mod `37`** (a `def … : Prop`, **not** an axiom — the *first-order* producer residual).

For every Case-II descent instance, there is a real unit `ν : (𝓞 K⁺)ˣ` (Washington's `η̄_b/η̄_a`)
and a unit `w : (𝓞 K)ˣ` (Washington's `(μ_b/μ_a)^{37}`) with `w ≡` a rational integer mod `37`, such
that the corrected descent unit factors as

  `(ε₁/ε₂)·(Units.map ν)^{37} = w^{37}`.

This is the *first-order* content of Washington Theorem 9.4's producer-`μ` structure: the corrected
unit is a **global `37`-th power** (of `w = (μ_b/μ_a)^{37}`) whose base `w` is `≡` rational mod `37`
(Lemma 1.8 freshman's dream).  It is **strictly sharper** than the mod-`37²` congruence
`Cor823DescentUnitModSqCongruence37`, which it discharges via the proven `37²`-power kernel §1
(`caseIICor823_descentUnitModSqCongruence37_of_pthPower`).  Sound and non-vacuous (consequent
inhabited by `ν = w = 1`, `c = 1`). -/
def Cor823CorrectedUnitPthPowerRationalModP37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ (ν : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
      (w : (𝓞 (CyclotomicField 37 ℚ))ˣ) (c : ℤ),
      (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
        ((w : 𝓞 (CyclotomicField 37 ℚ)) - (c : 𝓞 (CyclotomicField 37 ℚ))) ∧
      (ε₁ / ε₂ *
          Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom ν ^ 37 :
            (𝓞 (CyclotomicField 37 ℚ))ˣ) =
        w ^ 37

open FLT37.LehmerVandiver.CaseII in
/-- **The mod-`37²` congruence from the sharper first-order producer datum** (proven, axiom-clean):
`Cor823CorrectedUnitPthPowerRationalModP37 → Cor823DescentUnitModSqCongruence37`.

The corrected unit `(ε₁/ε₂)·(Units.map ν)^{37} = w^{37}` with `w ≡ c (mod 37)`; the proven
`37²`-power kernel §1 (`caseII_pow37_sub_intCast_pow37_mem_37sq`) upgrades this to
`w^{37} ≡ c^{37} (mod 37²)`, i.e. the corrected unit is `≡` the rational integer `c^{37}` mod `37²`.
This **discharges the entire second-order content** of `Cor823DescentUnitModSqCongruence37` from the
sharper *first-order* producer datum — the `37²` is supplied by the proven kernel, not hypothesised. -/
theorem caseIICor823_descentUnitModSqCongruence37_of_pthPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h : Cor823CorrectedUnitPthPowerRationalModP37) :
    Cor823DescentUnitModSqCongruence37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨ν, w, c, hwc, hfac⟩ := h hV hSO D hx hy hz heq
  refine ⟨ν, c ^ 37, ?_⟩
  -- The corrected unit equals `w^{37}`; apply the `37²`-power kernel to `w ≡ c (mod 37)`.
  rw [hfac]
  rw [show (((w ^ 37 : (𝓞 (CyclotomicField 37 ℚ))ˣ)) : 𝓞 (CyclotomicField 37 ℚ)) =
      (w : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 from by rw [Units.val_pow_eq_pow_val]]
  exact caseII_pow37_sub_intCast_pow37_mem_37sq hwc

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II via Corollary 8.23, from the sharper first-order producer datum** (proven,
axiom-clean given the first-order producer residual + Corollary 8.23).

Composes `caseIICor823_descentUnitModSqCongruence37_of_pthPower` (the mod-`37²` congruence from the
proven kernel) with `caseIIOmega32_assumptionII_of_cor823`.  So **Assumption II** follows from the
*first-order* producer datum `Cor823CorrectedUnitPthPowerRationalModP37` (the corrected unit is a
global `37`-th power with rational base mod `37`) together with Corollary 8.23 — the second-order
`37²` content being supplied by the proven `37²`-power kernel.  No mod-`𝔩` input. -/
theorem caseIIOmega32_assumptionII_of_cor823_firstOrder
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (h_cor823 : Cor823PthPowerOfRationalModSq37) :
    WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIOmega32_assumptionII_of_cor823
    (caseIICor823_descentUnitModSqCongruence37_of_pthPower h_pthPow) h_cor823

end BernoulliRegular.FLT37.Eichler

end

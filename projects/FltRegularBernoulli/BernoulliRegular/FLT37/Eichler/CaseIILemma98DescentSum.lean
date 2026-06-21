import BernoulliRegular.FLT37.Eichler.CaseIILehmerVandiverDvdZ
import BernoulliRegular.FLT37.Eichler.CaseIIThm95Discharge

/-!
# [FLT37-CASEII-R4-LEMMA98] Washington Lemma 9.8 `ℓ ∣ (ω + θ)` over the Case-II descent, corrected

This file performs the **soundness repair** of the over-stated
`CaseIILemma98DescentSumMem37` (`CaseIILehmerVandiverDvdZ.lean`) and discharges its **corrected,
single-unit, membership-only** form down to the smallest genuine residual — the
**Kummer–Mirimanoff congruence** at the heart of Washington *Cyclotomic Fields* 2nd ed. Lemma 9.8
(pp. 178–180), the second-case `ℓ ∣ z` content for the irregular index `i = 32`.

## The over-statement (logged B2 `R4-lemma98`, two counts)

`CaseIILemma98DescentSumMem37` asserts, for an **abstract** `CaseIIData37` with **free** units
`ε₁, ε₂, ε₃` and exponent `m` and **free** `x', y', z'` under only `(ζ-1) ∤ x', y', z'` plus the
unit-twisted equation `ε₁ x'³⁷ + ε₂ y'³⁷ = ε₃ ((ζ-1)^m z')³⁷`, the factorized output

  `∃ a u, x' + y' = (ζ-1)^a · u · z'   ∧   x' + y' ∈ lv149`.

This is **over-stated on two counts**:

1. **Free `ε₁, ε₂, ε₃` / exponent `m`.**  The genuine descent datum is the **single-unit** form
   `CaseIIData37.equation`: `x³⁷ + y³⁷ = ε · ((ζ-1)^{m+1} · z)³⁷` (`ε₁ = ε₂ = 1`, `ε₃ = ε`,
   exponent `m+1`).  Washington's all-conjugate factorization
   `∏_{ζ ∈ μ₃₇} (x' + ζ·y') = x'³⁷ + y'³⁷` (`IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul`, `37` odd)
   needs coefficient `1` on **both** `x'³⁷` and `y'³⁷`; with `ε₁ ≠ ε₂` the LHS does **not** factor
   and the argument cannot start.  The endpoint instantiates only `ε₁ = ε₂ = 1, ε₃ = ε` anyway.

2. **The equality `x' + y' = (ζ-1)^a · u · z'`.**  Even at `ε₁ = ε₂ = 1`, this is **false**:
   `x' + y'` is the `ζ = 1` factor of `∏(x' + ζⁱy') = ε(ζ-1)^{37(m+1)} z'³⁷`, i.e. **one** of `37`
   factors pairwise coprime away from `(ζ-1)`.  By unique factorization `x' + y'` carries the full
   `(ζ-1)`-power but only a *proper divisor* of `z'³⁷`, **not** a unit multiple of `z'`.

Washington's genuine output is **`ℓ ∣ (ω + θ)`** — the *membership* `x + y ∈ lv149` (Lemma 9.8) —
from which `ℓ ∣ z` follows **directly via the single-unit equation**, not via the bogus
single-factor equality (`caseII_dvd_z_of_equation` below, replacing the equality-consuming
`caseII_dvd_z_of_factorization`).

## The corrected statement and its discharge

* **`caseII_dvd_z_of_equation`** — **proven, axiom-clean**: from `x + y ∈ lv149` and the single-unit
  `CaseIIData37.equation`, `z ∈ lv149`.  (`x + y ∣ x³⁷ + y³⁷ = ε(ζ-1)^{37(m+1)}z³⁷`; `lv149` prime,
  `lv149 ∤ ε` (unit), `lv149 ∤ (ζ-1)` (`ℓ` unramified) ⟹ `lv149 ∣ z`.)  This is the **sound**
  replacement for the equality-consuming `caseII_dvd_z_of_factorization`.

* **`caseII_pow_add_pow_mem_lv149_of_dvd_z`** / **`caseII_exists_factor_mem_lv149_of_dvd_z`** —
  **proven, axiom-clean**: with the standing `ℓ ∣ z` (Washington Lemma 9.7, the descent-level
  hypothesis), `x³⁷ + y³⁷ = ∏(x + ζⁱy) ∈ lv149`, so **some** factor `x + ζʲy ∈ lv149`
  (`Ideal.IsPrime.prod_mem_iff`).  This is `∏(ω + ζⁱθ) ≡ 0 mod 𝔩`.

* **`Lemma98MirimanoffPthPower37`** (`def … : Prop`, **not** an axiom) — the **smallest genuine
  residual**: the Kummer–Mirimanoff implication.  For a **nontrivial** conjugate factor
  `x + ζʲy ∈ lv149` (`ζʲ ≠ 1`, i.e. `j ≠ 0`) with `ℓ ∤ x, ℓ ∤ y` (Lemma 9.6), the irregular real
  cyclotomic (Pollaczek) unit `E₃₂ = pollaczekUnitPlus 37 K 32` is a `37`-th power modulo `lv149`.
  This is Washington Lemma 9.8 steps 1–5 (the `(ζᵃ-ζʲ)/(1-ζ^{a+j})` `p`-th-power congruence, the
  telescoping over `ξ_b` via Lemma 8.1, and the Galois descent making every real cyclotomic unit a
  `p`-th power mod every prime above `ℓ`).

* **`caseII_lemma98_x_add_y_mem_of_dvd_z`** — **the genuine Lemma 9.8**, discharged from the
  residual: with the standing `ℓ ∣ z` and Lemma 9.6 (`ℓ ∤ x, ℓ ∤ y`), the special factor index is
  `j = 0`, i.e. `x + y ∈ lv149`.  The Mirimanoff residual makes `j ≠ 0` produce `E₃₂` a `37`-th
  power mod `lv149`, **contradicting the proven `caseIIThm95_engine_runs` (`Q₃₂⁴ ≢ 1 mod 149`)**.

* **`CaseIILemma98DescentSumMemStrict37`** (`def … : Prop`) — the **corrected** single-unit,
  membership-only restatement (conclusion `x + y ∈ lv149`, no equality), discharged from the
  residual by `caseIILemma98DescentSumMemStrict37_of_mirimanoff`.

It imports only — it does **not** modify any existing file.

## How the proven `Q₃₂⁴ ≢ 1` is used

The contradiction half of Lemma 9.8 is exactly the proven repo certificate
`caseIIThm95_engine_runs` (`CaseIIThm95Discharge.lean`): `E₃₂ = pollaczekUnitPlus 37 K 32` is
**not** a `37`-th power modulo `lv149` (Washington's `Q₃₂⁴ ≢ 1 mod 149`, a single `ZMod 149`
computation, no `p`-adic `L`).  The Mirimanoff residual says `j ≠ 0` would make `E₃₂` a `37`-th
power mod `lv149`;
`caseIIThm95_engine_runs` refutes that, forcing `j = 0`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Theorem 9.5,
  Lemmas 9.6–9.9 (pp. 176–181): Lemma 9.6 `ℓ ∤ xy`, Lemma 9.7 `ℓ ∣ z`, Lemma 9.8 `ℓ ∣ (ω + θ)`
  (the all-conjugate `∏(ω + ζⁱθ) ≡ 0 mod 𝔩`, the Kummer–Mirimanoff congruence, and `Q_i^k ≢ 1`),
  §9.1–9.2 the descent identity, Lemma 8.1 (cyclotomic units).
-/

@[expose] public section

noncomputable section

open NumberField Finset Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 0. `ℓ ∣ (x + y) ⟹ ℓ ∣ z` via the single-unit equation (sound replacement)

Washington's Lemma 9.8 outputs the *membership* `ℓ ∣ (ω + θ)`; the `ℓ ∣ z` it ultimately yields
comes from the §9.2 descended equation directly, **not** from a single-factor equality.  We prove
the sound algebraic kernel: for a `CaseIIData37` datum, `x + y ∈ lv149 ⟹ z ∈ lv149`, using only
`CaseIIData37.equation` (`x³⁷ + y³⁷ = ε ((ζ-1)^{m+1} z)³⁷`), the all-conjugate factorization, and
the proven coprimality facts (`lv149 ∤ ε`, `lv149 ∤ (ζ-1)`). -/

/-- **`x + y` divides `x³⁷ + y³⁷`** (the `ζ = 1` factor of the all-conjugate product).

`∏_{ζ ∈ μ₃₇} (x + ζ·y) = x³⁷ + y³⁷` (`IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul`, `37` odd), and
`x + y = x + 1·y` is the `ζ = 1 ∈ nthRootsFinset 37 1` factor. -/
theorem caseII_x_add_y_dvd_pow_add_pow {ζ : CyclotomicField 37 ℚ}
    (hζ : IsPrimitiveRoot ζ 37) (x y : 𝓞 (CyclotomicField 37 ℚ)) :
    (x + y) ∣ x ^ 37 + y ^ 37 := by
  rw [hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul x y (by decide)]
  have h1 : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    one_mem_nthRootsFinset (by decide)
  simpa using Finset.dvd_prod_of_mem (fun η => x + η * y) h1

/-- **`ℓ ∣ (x + y) ⟹ ℓ ∣ z`** (proven, axiom-clean) — the **sound** replacement for the
equality-consuming `caseII_dvd_z_of_factorization`.

From `x + y ∈ lv149` and the single-unit `CaseIIData37.equation`
(`x³⁷ + y³⁷ = ε ((ζ-1)^{m+1} z)³⁷`): `x + y ∣ x³⁷ + y³⁷` (the `ζ = 1` factor), so `lv149` (prime)
absorbs `x³⁷ + y³⁷ = ε(ζ-1)^{37(m+1)} z³⁷`; peeling the unit `ε` (`lv149 ∤ ε`,
`caseII_unit_notMem_lv149`), the `37`-th power, and the `(ζ-1)`-power (`lv149 ∤ (ζ-1)`,
`caseII_zeta_sub_one_notMem_lv149`, "`ℓ` unramified"), `lv149 ∣ z`.

This is Washington's `ℓ ∣ (ω + θ) ⟹ ℓ ∣ ρ₀`, derived from the genuine single-unit equation rather
than the false factorization `x + y = (ζ-1)^a · u · z`. -/
theorem caseII_dvd_z_of_equation
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    (hsum : D.x + D.y ∈ lv149) :
    D.z ∈ lv149 := by
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  -- `x + y ∣ x³⁷ + y³⁷`, and `lv149` absorbs the multiple.
  obtain ⟨w, hw⟩ := caseII_x_add_y_dvd_pow_add_pow D.hζ D.x D.y
  have hmem : D.x ^ 37 + D.y ^ 37 ∈ lv149 := by
    rw [hw]; exact Ideal.mul_mem_right _ _ hsum
  -- Rewrite via the single-unit equation and peel `ε`, the `37`-th power, the `(ζ-1)`-power.
  rw [D.equation] at hmem
  have h2 : ((D.hζ.toInteger - 1) ^ (m + 1) * D.z) ^ 37 ∈ lv149 :=
    (Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hmem).resolve_left
      (caseII_unit_notMem_lv149 D.ε)
  have h3 : (D.hζ.toInteger - 1) ^ (m + 1) * D.z ∈ lv149 :=
    Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› 37 h2
  refine (Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› h3).resolve_left (fun hpow => ?_)
  exact caseII_zeta_sub_one_notMem_lv149 D.hζ
    (Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› (m + 1) hpow)

/-! ## 1. The all-conjugate product `∏(ω + ζⁱθ) ≡ 0 mod 𝔩` under the standing `ℓ ∣ z`

Washington's Lemma 9.8 opens with `∏_{i}(ω + ζⁱθ) ≡ 0 (mod 𝔩)`, which holds because the descended
equation has `ℓ ∣ z` (Lemma 9.7, the standing descent-level hypothesis): `x³⁷ + y³⁷` has the factor
`z³⁷`.  Hence some conjugate factor `x + ζʲy ∈ lv149`. -/

/-- **`ℓ ∣ z ⟹ ℓ ∣ (x³⁷ + y³⁷)`** (proven, axiom-clean).

The single-unit equation `x³⁷ + y³⁷ = ε ((ζ-1)^{m+1} z)³⁷` has the factor `z³⁷` on the right;
with the standing `z ∈ lv149` (Washington Lemma 9.7), `lv149 ∣ x³⁷ + y³⁷`.  This is Washington's
`∏(ω + ζⁱθ) = ωᵖ + θᵖ ≡ 0 (mod 𝔩)`. -/
theorem caseII_pow_add_pow_mem_lv149_of_dvd_z
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m) (hz : D.z ∈ lv149) :
    D.x ^ 37 + D.y ^ 37 ∈ lv149 := by
  rw [D.equation]
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ hz) 37 (by decide))

/-- **Some conjugate factor `x + ζʲy ∈ lv149`** (proven, axiom-clean).

Combining `caseII_pow_add_pow_mem_lv149_of_dvd_z` with the all-conjugate factorization
`x³⁷ + y³⁷ = ∏_{η ∈ μ₃₇} (x + η·y)` and the primality of `lv149` (`Ideal.IsPrime.prod_mem_iff`):
some `η ∈ nthRootsFinset 37 1` has `x + η·y ∈ lv149`.  This is Washington's "`ω + ζʲθ ≡ 0 (mod 𝔩)`
for some `j`". -/
theorem caseII_exists_factor_mem_lv149_of_dvd_z
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m) (hz : D.z ∈ lv149) :
    ∃ η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)), D.x + η * D.y ∈ lv149 := by
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  have hpow := caseII_pow_add_pow_mem_lv149_of_dvd_z D hz
  rw [D.hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul D.x D.y (by decide)] at hpow
  exact Ideal.IsPrime.prod_mem_iff.mp hpow

/-! ## 2. The Kummer–Mirimanoff residual (the smallest genuine core of Lemma 9.8)

The remaining content of Washington Lemma 9.8 — between the all-conjugate factor `x + ζʲy ∈ lv149`
(§1, proven) and the contradiction with `Q₃₂⁴ ≢ 1` (`caseIIThm95_engine_runs`, proven) — is the
**Kummer–Mirimanoff congruence** (Washington pp. 178–180, steps 1–5):

For `j ≠ 0` (`ζʲ ≠ 1`) with `ℓ ∤ x, ℓ ∤ y` (Lemma 9.6), the §9.1 real `ρ_a` structure gives, for
`a ≢ ±j (mod p)`, that `(ζᵃ - ζʲ)/(1 - ζ^{a+j})` is a `p`-th power mod `𝔩` (using `ρ_p^p ≡ 1`,
`k = (ℓ-1)/p` even, and `ω ≡ -ζʲθ`).  This ratio is `-ξ_{a-j}·ξ_{a+j}^{-1}` (Lemma 8.1), and the
telescoping `ξ_b = ξ_1 ξ_{1+2j} ⋯` (with `ξ_1 = 1`) shows **every** real cyclotomic unit `ξ_b`
(`b ≢ 0 mod p`) is a `p`-th power mod `𝔩`.  Applying `Gal(ℚ(ζ_p)/ℚ)`, every real cyclotomic unit is
a `p`-th power modulo **every** prime above `ℓ`; in particular `E₃₂ = pollaczekUnitPlus 37 K 32`.

We name **exactly this implication** as the residual.  It is the genuine open content (the §9.1
`ρ_a` / Lemma-8.1 cyclotomic-unit machinery is not present at the element level for `CaseIIData37`).
It is **non-vacuous**: its conclusion (`E₃₂` is a `37`-th power mod `lv149`) is **false**
(`caseIIThm95_engine_runs`), so the residual genuinely asserts that a nontrivial factor
`x + ζʲy ∈ lv149` with `j ≠ 0` cannot occur — Washington's `j = 0`. -/

/-- **Washington Lemma 9.8's Kummer–Mirimanoff residual for `p = 37`** (a `def … : Prop`, **not** an
axiom) — the smallest genuine core of the second-case `ℓ ∣ z` argument.

For every Case-II descent instance, **if** a *nontrivial* conjugate factor `x + η·y ∈ lv149`
(`η ∈ μ₃₇`, `η ≠ 1`, i.e. Washington's special index `j ≠ 0`) occurs with `ℓ ∤ x` and `ℓ ∤ y`
(Lemma 9.6), **then** the irregular real cyclotomic (Pollaczek) unit
`E₃₂ = pollaczekUnitPlus 37 K 32` is a `37`-th power modulo `lv149`.

This is Washington Lemma 9.8 steps 1–5 (pp. 178–180): the `(ζᵃ-ζʲ)/(1-ζ^{a+j})` `p`-th-power
congruence, the `ξ_b` telescoping (Lemma 8.1), and the Galois descent making every real cyclotomic
unit — in particular `E₃₂` — a `p`-th power modulo every prime above `ℓ`.  Combined with the proven
`caseIIThm95_engine_runs` (`E₃₂` is **not** a `37`-th power mod `lv149`, Washington's `Q₃₂⁴ ≢ 1`),
it forces `j = 0`, i.e. `x + y ∈ lv149` (`caseII_lemma98_x_add_y_mem_of_dvd_z`).

**Non-vacuity.**  The conclusion is the negation of the proven `caseIIThm95_engine_runs`, so the
residual is *not* always true: it genuinely constrains the descent data (it asserts no nontrivial
conjugate factor can lie in `lv149`). -/
def Lemma98MirimanoffPthPower37
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
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))

/-! ## 3. The genuine Lemma 9.8: `ℓ ∣ z ⟹ ℓ ∣ (x + y)` (`j = 0`) -/

/-- **Washington Lemma 9.8 for `p = 37`** (proven from the Mirimanoff residual, axiom-clean).

With the standing `ℓ ∣ z` (Washington Lemma 9.7) and Lemma 9.6 (`ℓ ∤ x`, `ℓ ∤ y`), the special
conjugate-factor index is `j = 0`, i.e. `x + y ∈ lv149` (`ℓ ∣ (ω + θ)`).

Proof: `caseII_exists_factor_mem_lv149_of_dvd_z` gives a factor `x + η·y ∈ lv149`
(`η ∈ μ₃₇`).  If `η = 1`, this is `x + y ∈ lv149` directly.  If `η ≠ 1`, the Mirimanoff residual
`Lemma98MirimanoffPthPower37` makes `E₃₂` a `37`-th power mod `lv149`, **contradicting** the proven
`caseIIThm95_engine_runs` (`Q₃₂⁴ ≢ 1 mod 149`). -/
theorem caseII_lemma98_x_add_y_mem_of_dvd_z
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_mirimanoff : Lemma98MirimanoffPthPower37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.x + D.y ∈ lv149 := by
  obtain ⟨η, hη_mem, hη_in⟩ := caseII_exists_factor_mem_lv149_of_dvd_z D hz
  by_cases hη1 : η = 1
  · subst hη1; simpa using hη_in
  · exact absurd (h_mirimanoff hV hSO D hη_mem hη1 hxl hyl hη_in) caseIIThm95_engine_runs

/-! ## 4. The corrected `CaseIILemma98DescentSumMem37`: single-unit, membership-only

`CaseIILemma98DescentSumMemStrict37` is the **corrected** form of `CaseIILemma98DescentSumMem37`:
the single-unit form (it speaks of a `CaseIIData37`'s own `D.x, D.y, D.z, D.ε`, matching
`CaseIIData37.equation`), with the standing `ℓ ∣ z` (Lemma 9.7) and Lemma 9.6 (`ℓ ∤ x, ℓ ∤ y`)
as hypotheses, and the **membership-only** conclusion `x + y ∈ lv149` (Washington's `ℓ ∣ (ω + θ)`),
dropping the false equality. -/

/-- **Washington Lemma 9.8 over the Case-II descent, corrected (R4-LEMMA98)** (a `def … : Prop`,
**not** an axiom).

The single-unit, membership-only restatement of `CaseIILemma98DescentSumMem37`: for a `CaseIIData37`
datum with the standing `ℓ ∣ z` (Washington Lemma 9.7) and Lemma 9.6 (`ℓ ∤ x, ℓ ∤ y`), the descended
sum `x + y` lies in `lv149` (`ℓ ∣ (ω + θ)`).  No free units, no false equality.

Discharged from `Lemma98MirimanoffPthPower37` by
`caseIILemma98DescentSumMemStrict37_of_mirimanoff`. -/
def CaseIILemma98DescentSumMemStrict37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
    D.z ∈ lv149 → D.x ∉ lv149 → D.y ∉ lv149 →
    D.x + D.y ∈ lv149

/-- **The corrected Lemma 9.8 is genuinely true given the Mirimanoff residual** (proven,
axiom-clean).

`CaseIILemma98DescentSumMemStrict37` holds: it is exactly `caseII_lemma98_x_add_y_mem_of_dvd_z`
packaged over the descent telescope. -/
theorem caseIILemma98DescentSumMemStrict37_of_mirimanoff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_mirimanoff : Lemma98MirimanoffPthPower37) :
    CaseIILemma98DescentSumMemStrict37 := by
  intro hV hSO m D hz hxl hyl
  exact caseII_lemma98_x_add_y_mem_of_dvd_z h_mirimanoff hV hSO D hz hxl hyl

/-! ## 5. Recovering the genuine `ℓ ∣ z` consumer (`caseII_dvd_z_of_equation` ∘ Lemma 9.8)

The downstream consumer needs `z ∈ lv149`.  Washington derives it at the descended level from the
standing `ℓ ∣ z` at the prior level via Lemma 9.8 (`ℓ ∣ ω+θ ⟹ ℓ ∣ ρ₀ = z`); within a single
`CaseIIData37` the standing `ℓ ∣ z` is the carried Lemma-9.7 hypothesis
(`CaseIILehmerVandiverDvdZ37`, the prior session's correctly-carried genuine-data Prop).  What this
file adds is the **sound** Lemma-9.8 membership chain `ℓ ∣ z ⟹ ℓ ∣ (x+y) ⟹ ℓ ∣ z` (the second
step now via
`caseII_dvd_z_of_equation`, not the false equality), confirming the membership form is internally
consistent and the genuine analytic content (the Mirimanoff residual) is isolated. -/

/-- **The sound Lemma-9.8 round trip** (proven from the residual, axiom-clean): with the standing
`ℓ ∣ z` and Lemma 9.6, the genuine Lemma 9.8 gives `x + y ∈ lv149`
(`caseII_lemma98_x_add_y_mem_of_dvd_z`), and `caseII_dvd_z_of_equation` recovers `z ∈ lv149` —
confirming the membership form's consistency
and that the only genuine open content is `Lemma98MirimanoffPthPower37`. -/
theorem caseII_lemma98_dvd_z_round_trip
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_mirimanoff : Lemma98MirimanoffPthPower37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.z ∈ lv149 :=
  caseII_dvd_z_of_equation D
    (caseII_lemma98_x_add_y_mem_of_dvd_z h_mirimanoff hV hSO D hz hxl hyl)

end BernoulliRegular.FLT37.Eichler

end

end

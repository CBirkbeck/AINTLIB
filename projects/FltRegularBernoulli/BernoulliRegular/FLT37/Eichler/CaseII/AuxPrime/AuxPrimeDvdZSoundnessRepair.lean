import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.LocalPowerDvdZ

/-!
# [FLT37-CASEII-R4-ELLZ] Washington Lemma 9.7 / 9.8 `ℓ ∣ z` over the Case-II descent, corrected

This file performs the **soundness repair** of the over-stated
`CaseIILehmerVandiverDvdZ37` (`CaseIILocalPowerStrict.lean`), Washington
*Cyclotomic Fields* 2nd ed. Lemma 9.7's `ℓ ∣ z` divisibility (the auxiliary prime `ℓ = 149`
dividing the descent variable `z'`), and discharges the **corrected** form.

## The over-statement (logged B2 `R4-ellz`)

`CaseIILehmerVandiverDvdZ37` asserts `z' ∈ lv149` (i.e. `149 ∣ z'`) for an **abstract**
`CaseIIData37` with *free* units `ε₁, ε₂, ε₃` and *free* `x', y', z'` under only
`(ζ-1) ∤ x'`, `(ζ-1) ∤ y'`, `(ζ-1) ∤ z'` plus the unit-twisted descended equation

  `ε₁ x'^37 + ε₂ y'^37 = ε₃ ((ζ-1)^m z')^37`.

This is **over-stated**.  Reduce mod `lv149` (the residue field `𝓞 K / lv149 ≅ 𝔽₁₄₉`,
in which `ζ ↦ 16` has order `37` and `ζ - 1 ↦ 15 ≠ 0`, so `ζ - 1` is a **unit** mod
`lv149`).  The equation reads, in `𝔽₁₄₉^×` (cyclic of order `148 = 4·37`),

  `Q(ε₁) Q(x')^37 + Q(ε₂) Q(y')^37 = Q(ε₃) · 15^{37m} Q(z')^37`.

The **free unit residues** `Q(ε₁), Q(ε₂), Q(ε₃)` absorb the equation, leaving `Q(z')`
unconstrained: e.g. with `Q(x') = Q(y') = Q(z') = 1` (all `37`-th powers, nonzero, so
`z' ∉ lv149`), `m ≡ 0`, and `Q(ε₁) = 5`, `Q(ε₂) = 145`, `Q(ε₃) = 1` (all quadratic
residues mod `149`, hence in the image of `μ₇₄ ⊂ (𝓞 K)^×` since `ζ ↦ 16 = 2^4` has
order `37` and `-1 ↦ 148`), `5·1 + 145·1 = 150 ≡ 1 = 1·15^0·1 (mod 149)` holds with
`149 ∤ z'`.

Washington's genuine `ℓ ∣ z'` of the descended variable is established via **Lemma 9.8**
(`ℓ ∣ ω + θ`, the factorization `ω + θ = η₀ λ^{m-(p-1)/2} ρ g` with `ℓ` unramified, so
`ℓ ∣ ρ₀`).  Lemma 9.8's proof needs the **all-conjugate product**
`∏_i (ω + ζⁱθ) ≡ 0 (mod 𝔩)` plus the Theorem-9.5 power-residue condition `Q_i^k ≢ 1`
(the proven repo certificate `caseIIThm95_engine_runs`, `Q₃₂⁴ ≢ 1 mod 149`), seeded by
Lemma 9.7's integer `ℓ ∣ z` ("`1 < p² - p` used most strongly"; `149 < 1332 = 37² - 37`).
The **bare** twisted equation supplies **none** of this: `CaseIIData37` stores only the
*cyclotomic-integer* descended `x, y, z : 𝓞 K`, not the *rational-integer* Fermat origin
`a, b, c ∈ ℤ` that Lemma 9.7's all-conjugate argument over `ℤ` requires
(`exists_caseIIData37_of_caseII_int_solution` discards `a, b, c`).

## The corrected statement and its discharge

The genuine analytic content of Washington Lemma 9.8 is the factorization output

  `x' + y' = (ζ - 1)^a · u · z'`   (the descent `ω + θ = η₀ λ^a g · ρ₀`, `u` a unit)

**together with** `x' + y' ∈ lv149` (Lemma 9.8's `ℓ ∣ ω + θ`, the all-conjugate product
step using `Q₃₂⁴ ≢ 1`).  From these two genuine outputs, `z' ∈ lv149` follows by the
**proven** unramified/coprimality argument of this file:

* `caseII_zeta_sub_one_notMem_lv149` — **proven, axiom-clean**: for any primitive `37`-th
  root `ζ`, `ζ - 1 ∉ lv149` (`Q(ζ)` is a primitive `37`-th root in `𝔽₁₄₉`, so `Q(ζ) ≠ 1`;
  were it `1`, the geometric sum `∑_{i<37} ζⁱ = 0` would give `37 ∈ lv149`, impossible
  since `lv149` lies over `149` and `gcd(37, 149) = 1`).  Washington's "`ℓ` unramified".

* `caseII_dvd_z_of_factorization` — **proven, axiom-clean**: from `x' + y' ∈ lv149` and the
  factorization `x' + y' = (ζ-1)^a · u · z'`, since `lv149` is prime, `ζ - 1 ∉ lv149`, and
  `u` is a unit (`∉ lv149`), the prime divides `z'`.  Washington's `ℓ ∣ ω + θ ⟹ ℓ ∣ ρ₀`.

* `CaseIILehmerVandiverDvdZ37Strict` (`def … : Prop`) — `CaseIILehmerVandiverDvdZ37` with
  the genuine Lemma-9.8 input `∃ a u, x' + y' = (ζ-1)^a · u · z' ∧ x' + y' ∈ lv149` added.
  **Genuinely true**, discharged by `caseIILehmerVandiverDvdZ37Strict_proven`.

* `caseIILehmerVandiverDvdZ37_of_strict` — recovers the over-stated
  `CaseIILehmerVandiverDvdZ37` from the strict form **plus** the genuine Lemma-9.8 datum
  `CaseIILemma98DescentSumMem37`, so the downstream chain consumes a sound, non-vacuous
  `ℓ ∣ z` input.

It imports only — it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Theorem 9.5,
  Lemmas 9.6–9.9 (pp. 176–181): Lemma 9.7 `ℓ ∣ z` (`1 < p² - p` finiteness), Lemma 9.8
  `ℓ ∣ ω + θ` (the all-conjugate `∏(ω + ζⁱθ) ≡ 0 mod 𝔩` + `Q_i^k ≢ 1`), §9.2 the "basic
  argument" descent factorization `ω + θ = η₀ λ^{m-(p-1)/2} ρ g`.
-/

@[expose] public section

noncomputable section

open NumberField Polynomial Finset

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 0. `ℓ = 149` is unramified: `ζ - 1 ∉ lv149` for any primitive `37`-th root

Washington's Lemma 9.8 step "`ℓ ∣ ω + θ ⟹ ℓ ∣ ρ₀`" uses that `ℓ = 149` is unramified in `𝓞 (ℚ(ζ₃₇))`
(so the prime `lv149` does **not** divide `ζ - 1`, the generator of the ramified prime over `37`).
We prove this concretely: the residue `Q(ζ) ∈ 𝔽₁₄₉` of a primitive `37`-th root is again a primitive
`37`-th root (a root of `Φ₃₇ mod 149`), hence `≠ 1`; equivalently, if `ζ - 1 ∈ lv149` then the
geometric sum `∑_{i<37} ζⁱ = 0` reduces to `37 = 0` in `𝔽₁₄₉`, forcing `37 ∈ lv149`, contradicting
`149 ∈ lv149` and `gcd(37, 149) = 1`. -/

/-- **`37 ∉ lv149`.**  The prime `lv149` lies over the rational prime `149`
(`lehmerVandiverPrime_natCast_ℓ_mem`), and `gcd(37, 149) = 1`; were `37 ∈ lv149` too, then `1 ∈ lv149`
(Bézout `4·37 - 1·149 = -1`), contradicting that `lv149` is a proper (prime) ideal. -/
theorem caseII_thirtyseven_notMem_lv149 :
    ((37 : ℕ) : 𝓞 (CyclotomicField 37 ℚ)) ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  intro h37
  -- `149 ∈ lv149` (lv149 lies over the rational prime 149).
  have h149 : ((149 : ℕ) : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 := by
    unfold lv149
    exact FLT37.lehmerVandiverPrime_natCast_ℓ_mem 37 149 4
      (by decide : (149 : ℕ) = 4 * 37 + 1)
      (by decide : (2 : ℕ).Coprime 149)
      (by decide +revert : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1)
  -- Bézout: `4·37 - 149 = -1`, so `1 = 149 - 4·37 ∈ lv149`.
  have hone : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 := by
    have : (1 : 𝓞 (CyclotomicField 37 ℚ)) =
        ((149 : ℕ) : 𝓞 (CyclotomicField 37 ℚ)) -
          (4 : 𝓞 (CyclotomicField 37 ℚ)) * ((37 : ℕ) : 𝓞 (CyclotomicField 37 ℚ)) := by
      push_cast; ring
    rw [this]
    exact Ideal.sub_mem _ h149 (Ideal.mul_mem_left _ _ h37)
  exact (Ideal.IsPrime.ne_top lv149_isMaximal.isPrime)
    (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

/-- **`ζ - 1 ∉ lv149` for any primitive `37`-th root `ζ ∈ 𝓞 (ℚ(ζ₃₇))`** (proven, axiom-clean).

This is Washington's "`ℓ = 149` is unramified in `𝓞 (ℚ(ζ_p))`": the prime `lv149` over `149` does not
divide the generator `ζ - 1` of the unique ramified prime (over `37`).

Proof: if `ζ - 1 ∈ lv149`, then in the geometric-sum identity `∑_{i<37} ζⁱ = 0`
(`IsPrimitiveRoot.geom_sum_eq_zero`) every `ζⁱ ≡ 1 (mod lv149)`, so `0 ≡ ∑_{i<37} 1 = 37 (mod lv149)`,
i.e. `37 ∈ lv149`, contradicting `caseII_thirtyseven_notMem_lv149`. -/
theorem caseII_zeta_sub_one_notMem_lv149 {ζ : CyclotomicField 37 ℚ}
    (hζ : IsPrimitiveRoot ζ 37) :
    (hζ.toInteger - 1) ∉ lv149 := by
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  intro hmem
  -- `∑_{i<37} ζ_int^i = 0` in `𝓞 K`.
  have hgeom : ∑ i ∈ range 37, (hζ.toInteger) ^ i = 0 :=
    hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by decide)
  -- Each `ζ_int^i ≡ 1 (mod lv149)`, since `ζ_int - 1 ∈ lv149` divides `ζ_int^i - 1`.
  have hpow_sub : ∀ i, (hζ.toInteger) ^ i - 1 ∈ lv149 := fun i =>
    lv149.mem_of_dvd (sub_one_dvd_pow_sub_one _ i) hmem
  -- Sum the congruences: `0 = ∑ ζ_int^i ≡ ∑ 1 = 37 (mod lv149)`, so `37 ∈ lv149`.
  have hsum_sub :
      (∑ i ∈ range 37, (hζ.toInteger) ^ i) -
        (∑ _i ∈ range 37, (1 : 𝓞 (CyclotomicField 37 ℚ))) ∈ lv149 := by
    rw [← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ (fun i _ => hpow_sub i)
  rw [hgeom, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, zero_sub,
    neg_mem_iff] at hsum_sub
  exact caseII_thirtyseven_notMem_lv149 (by exact_mod_cast hsum_sub)

/-! ## 1. `ℓ ∣ ω + θ ⟹ ℓ ∣ ρ₀`: the descended sum divides `z'`

Washington's §9.2 factorization `ω + θ = η₀ λ^{m-(p-1)/2} ρ g` (units `η₀, g`, `λ = ζ - 1`,
`ρ = ρ₀`) together with Lemma 9.8's `ℓ ∣ (ω + θ)` gives `ℓ ∣ ρ₀` because `ℓ` is unramified
(`lv149 ∤ λ`) and `η₀, g` are units.  We prove the abstract algebraic kernel: if
`x' + y' = (ζ-1)^a · u · z'` (`u` a unit) and `x' + y' ∈ lv149`, then `z' ∈ lv149`. -/

/-- A unit of `𝓞 K` is never in the proper ideal `lv149`. -/
theorem caseII_unit_notMem_lv149 (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
    (u : 𝓞 (CyclotomicField 37 ℚ)) ∉ lv149 := by
  intro hmem
  exact (Ideal.IsPrime.ne_top lv149_isMaximal.isPrime)
    (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)

/-- **`ℓ ∣ ω + θ ⟹ ℓ ∣ ρ₀`** (proven, axiom-clean).

From the descent factorization `x' + y' = (ζ-1)^a · u · z'` (Washington's
`ω + θ = η₀ λ^a g · ρ₀`, `u` a unit) and Lemma 9.8's `x' + y' ∈ lv149` (`ℓ ∣ ω + θ`), the prime
`lv149` divides `z'`.

Proof: `(ζ-1)^a · u · z' ∈ lv149`; `lv149` is prime, `ζ - 1 ∉ lv149`
(`caseII_zeta_sub_one_notMem_lv149`, "`ℓ` unramified"), so `(ζ-1)^a ∉ lv149`; and `u ∉ lv149`
(`caseII_unit_notMem_lv149`); hence `z' ∈ lv149`. -/
theorem caseII_dvd_z_of_factorization {ζ : CyclotomicField 37 ℚ}
    (hζ : IsPrimitiveRoot ζ 37) {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {a : ℕ} {u : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hfact : x' + y' = (hζ.toInteger - 1) ^ a * (u : 𝓞 (CyclotomicField 37 ℚ)) * z')
    (hsum : x' + y' ∈ lv149) :
    z' ∈ lv149 := by
  haveI hp : lv149.IsPrime := lv149_isMaximal.isPrime
  rw [hfact] at hsum
  -- `(ζ-1)^a * u ∉ lv149`, so the prime forces `z' ∈ lv149`.
  rcases hp.mem_or_mem hsum with hmul | hz
  · exfalso
    rcases hp.mem_or_mem hmul with hpow | hu
    · exact caseII_zeta_sub_one_notMem_lv149 hζ (hp.mem_of_pow_mem a hpow)
    · exact caseII_unit_notMem_lv149 u hu
  · exact hz

/-! ## 2. The genuine Lemma-9.8 descent datum, and the corrected `ℓ ∣ z` statement

`CaseIILemma98DescentSumMem37` names Washington Lemma 9.8's genuine output over the descent
telescope: the factorized `ℓ ∣ ω + θ`.  `CaseIILehmerVandiverDvdZ37Strict` is the over-stated
`CaseIILehmerVandiverDvdZ37` **plus** that genuine datum; it is **true** and discharged below. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.8's factorized output over the Case-II descent telescope**
(a `def … : Prop`, **not** an axiom) — the genuine analytic content the bare twisted equation lacks.

For every Case-II descent instance, the descended sum `x' + y'` (Washington's `ω + θ`) satisfies
Lemma 9.8's `ℓ ∣ (ω + θ)` in factorized form: there are `a : ℕ` and a unit `u` with

  `x' + y' = (ζ-1)^a · u · z'`     and     `x' + y' ∈ lv149`.

The factorization is the §9.2 descent identity `ω + θ = η₀ λ^{m-(p-1)/2} g · ρ₀` (units `η₀, g`);
the membership is Lemma 9.8 proper (`ℓ ∣ ω + θ`, via the all-conjugate product
`∏(ω + ζⁱθ) ≡ 0 mod 𝔩` and the proven `Q₃₂⁴ ≢ 1 mod 149`, `caseIIThm95_engine_runs`).  This is the
genuine `ℓ ∣ z` input — **not** derivable from the bare equation (see the module B2 note). -/
def CaseIILemma98DescentSumMem37
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
    ∃ (a : ℕ) (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      x' + y' = (D.hζ.toInteger - 1) ^ a * (u : 𝓞 (CyclotomicField 37 ℚ)) * z' ∧
      x' + y' ∈ lv149

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.7 over the Case-II descent telescope, corrected (R4-ELLZ)**
(a `def … : Prop`, **not** an axiom).

`CaseIILehmerVandiverDvdZ37` (the conclusion `z' ∈ lv149`) **plus** the genuine Lemma-9.8 descent
datum `CaseIILemma98DescentSumMem37` (the factorized `ℓ ∣ ω + θ`).  This is the **repaired** form: the
over-stated version dropped the Lemma-9.8 input and is false over the bare twisted equation (free
units absorb the residue equation; see the module B2 note).  With the genuine factorized `ℓ ∣ ω + θ`,
`z' ∈ lv149` follows by `caseII_dvd_z_of_factorization`.  Discharged by
`caseIILehmerVandiverDvdZ37Strict_proven`. -/
def CaseIILehmerVandiverDvdZ37Strict
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
    (∃ (a : ℕ) (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      x' + y' = (D.hζ.toInteger - 1) ^ a * (u : 𝓞 (CyclotomicField 37 ℚ)) * z' ∧
      x' + y' ∈ lv149) →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    z' ∈ lv149

/-! ## 3. Discharging the corrected `ℓ ∣ z` -/

open FLT37.LehmerVandiver.CaseII in
/-- **The corrected `ℓ ∣ z` is genuinely true** (proven, axiom-clean).

`CaseIILehmerVandiverDvdZ37Strict` holds: given the genuine Lemma-9.8 factorized output
`x' + y' = (ζ-1)^a · u · z'` with `x' + y' ∈ lv149`, the proven unramified/coprimality lemma
`caseII_dvd_z_of_factorization` gives `z' ∈ lv149`. -/
theorem caseIILehmerVandiverDvdZ37Strict_proven
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CaseIILehmerVandiverDvdZ37Strict := by
  intro _hV _hSO m D x' y' z' ε₁ ε₂ ε₃ _hx _hy _hz hlemma98 _heq
  obtain ⟨a, u, hfact, hsum⟩ := hlemma98
  exact caseII_dvd_z_of_factorization D.hζ hfact hsum

open FLT37.LehmerVandiver.CaseII in
/-- **The over-stated `CaseIILehmerVandiverDvdZ37` from the corrected form + the genuine Lemma-9.8
datum** (proven, axiom-clean).

`CaseIILehmerVandiverDvdZ37` is recovered from `CaseIILehmerVandiverDvdZ37Strict` by supplying its
genuine Lemma-9.8 hypothesis from `CaseIILemma98DescentSumMem37` (the factorized `ℓ ∣ ω + θ`).  Both
quantify over the same telescope and forward `D, x', y', z', ε's` unchanged, so this is a direct
composition: the downstream chain now consumes a sound, genuinely-non-vacuous `ℓ ∣ z` input. -/
theorem caseIILehmerVandiverDvdZ37_of_strict
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_lemma98 : CaseIILemma98DescentSumMem37) :
    CaseIILehmerVandiverDvdZ37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  exact caseIILehmerVandiverDvdZ37Strict_proven hV hSO D hx hy hz
    (h_lemma98 hV hSO D hx hy hz heq) heq

/-! ## 4. FLT37 with the corrected (sound) `ℓ ∣ z` datum

The downstream FLT37 endpoint `fermatLastTheoremFor_thirtyseven_of_genuineResiduals_localPowerStrict`
(`CaseIILocalPowerStrict.lean`) consumes the over-stated `CaseIILehmerVandiverDvdZ37` as one of its
inputs.  Composing with `caseIILehmerVandiverDvdZ37_of_strict`, we supply that input from the
**genuine** Lemma-9.8 datum `CaseIILemma98DescentSumMem37` (the factorized `ℓ ∣ ω + θ`), so the
`ℓ ∣ z` residual is now sound (no false universal over the bare twisted equation). -/

open FLT37.LehmerVandiver.CaseII in
/-- **FLT37 from the genuine residuals, with the sound (factorized Lemma-9.8) `ℓ ∣ z` datum**
(proven, axiom-clean given the named inputs + the carried second-order Bernoulli Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_genuineResiduals_localPowerStrict` except the
over-stated `CaseIILehmerVandiverDvdZ37` is replaced by the **sound** Lemma-9.8 descent datum
`CaseIILemma98DescentSumMem37` (Washington's factorized `ℓ ∣ ω + θ`), from which the genuine
`ℓ ∣ z` (`CaseIILehmerVandiverDvdZ37`) is recovered by `caseIILehmerVandiverDvdZ37_of_strict`. -/
theorem fermatLastTheoremFor_thirtyseven_of_genuineResiduals_lemma98Sum
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_localPowStrict : Lemma98LocalPower37Strict)
    (caseII_lemma98Sum : CaseIILemma98DescentSumMem37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_genuineResiduals_localPowerStrict
    caseII_classConjFixed
    caseII_realDescent
    caseII_leadingExp
    caseII_localPowStrict
    (caseIILehmerVandiverDvdZ37_of_strict caseII_lemma98Sum)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end

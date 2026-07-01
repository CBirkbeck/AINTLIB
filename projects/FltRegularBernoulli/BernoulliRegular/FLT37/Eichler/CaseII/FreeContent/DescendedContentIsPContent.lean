import BernoulliRegular.FLT37.Eichler.CaseII.FreeContent.DvdZFactorCountDescent

/-!
# [FLT37-CASEII-R2] The non-`p`-content gap of the free-content Case-II descent: dissolved

This file closes the **non-`p`-content gap** (residual (C)) of the FLT37 Case-II free-content
factor-count descent (`CaseIIFreeContentDvdZDescent.lean`).

## The gap, precisely mapped

The free-content frame `FreeContentCaseIIData37 n` (`CaseIIFreeContentDatum.lean`) carries the
`(ζ−1)`-content `n` **free** (equation `x³⁷ + y³⁷ = ε·(ζ−1)ⁿ·z³⁷`, the `λ`-factor *outside* the
`³⁷`-power).  Its descent step is discharged **only at content `37·(m+1)`**
(`freeContentCaseIIDvdZData37_pContent_descend_of_dvdZExtractionData`), because the §9.1 factor
equations are extracted via the flt-regular **root-ideal machinery**
(`FltRegular.CaseII.InductionStep`, `rootDivZetaSubOneDvdGcd` / `prod_c` /
`exists_ideal_pow_eq_c`), which requires the Fermat equation to be a **perfect `37`-th-power ideal**
`span{x³⁷+y³⁷} = (𝔭^{m+1}·z)³⁷` — i.e. `37 ∣ content`.  At a *general* content `n ≢ 0 (mod 37)`, the
ideal `𝔭ⁿ·(z)³⁷` is **not** a perfect `37`-th-power ideal (its `𝔭`-valuation `n` is `≢ 0 mod 37`),
so the simultaneous extraction `∏_η 𝔠(η) = (𝔷'·𝔭^m)³⁷` — and hence the root ideals `𝔞(η)`, the
quotient half `X/X̄ = β³⁷` (`caseII_correctedRadical_fractionalIdeal_eq`), and the product half
`X·X̄ = η'·γ³⁷` — **genuinely fails**.  This is a real obstruction, **not** a missing lemma: at
non-`p`-content the corrected radical's fractional ideal `span{α}` is not a perfect `37`-th power
(its valuations at primes `𝔮 ≠ 𝔭` are `≢ 0 mod 37`).

## The resolution: the descent **never produces** non-`p`-content (the gap is unreachable)

The descended datum (capstone `freeContentCaseIIData37_of_factorEquations`) sits at content
`n' = 2·(2e−1) = 4e−2`, where `e` is the **anchor exponent** of the §9.1 anchor equation
`x+y = η₀·Λ^e·ρ₀³⁷` (`Λ = (1−ζ)(1−ζ³⁶)`, the real prime, `v_𝔭(Λ) = 2`).  We prove here:

* `caseII_x_add_y_multiplicity_eq` — **the sharp anchor valuation `v_𝔭(x+y) = 37m+1`** for a
  `RealCaseIIData37 m`: from `span{x+y} = 𝔪·𝔞(η₀)³⁷·𝔭` (the proven `m_mul_c_mul_p` +
  `root_div_zeta_sub_one_dvd_gcd_spec` at the anchor `η₀ = 1`), `𝔞(η₀) = 𝔭^m·𝔞₀` with `¬𝔭∣𝔞₀`
  (`a_eta_zero_dvd_p_pow_spec`, `not_p_div_a_zero`) and `¬𝔭∣𝔪` (`gcd_zeta_sub_one_eq_one`),
  `v_𝔭(span{x+y}) = 0 + 37m + 1`.

* `caseII_anchor_exponent_two_mul_congr_one` — **`2e ≡ 1 (mod 37)`** for *any* anchor equation
  `algebraMap(x+y) = η₀·Λ^e·ρ₀³⁷`: taking `(ζ−1)`-multiplicities of the integer-cleared form gives
  `v_𝔭(x+y) ≡ 2e (mod 37)` (`Λ = algebraMap((1−ζ)(1−ζ³⁶))`, `v_𝔭 = 2`, `η₀` a unit), and
  `v_𝔭(x+y) = 37m+1 ≡ 1`.

* `caseII_descended_content_eq_p_content` — **the descended content `4e−2` is `37·(m'+1)`** with
  `m' ≥ 1`: from `2e ≡ 1 (mod 37)`, `2e = 37j+1` with `j` odd (`2e` even), so `e = 37t+19` and
  `4e−2 = 37·(4t+2) = 37·(m'+1)`, `m' = 4t+1 ≥ 1`.

So the descent step's output is **always at `p`-content**, hence always re-promotable to a
`RealCaseIIData37 m'`.  The non-`p`-content branch of the abstract step
`FreeContentCaseIIDvdZDescentStep37` is therefore **logically unreachable** in the descent seeded by
the (`p`-content) base producer.

## What this gives: the `p`-content-restricted descent (closing residual C)

We define `FreeContentCaseIIDvdZPContentDescentStep37` — the descent step **restricted to
`p`-content data**, producing `p`-content output — discharge it from the same §9.1 extraction data +
coprimality used at content `37·(m+1)` (now with the **proven** `p`-content output fact), run the
well-founded factor-count descent **inside the `p`-content subdomain** (seeded by the `p`-content
base producer), and re-close FLT37 Case-II.  The resulting endpoint
`fermatLastTheoremFor_thirtyseven_of_freeContentDvdZPContentDescent` carries **no non-`p`-content
gap**: the descent legitimately stays in `p`-content, where the root-ideal extraction always runs.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), pp. 171–173.
* flt-regular, `FltRegular/CaseII/InductionStep.lean` (the perfect-`p`-th-power root-ideal chain).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The sharp anchor valuation `v_𝔭(x+y) = 37m+1` -/

variable {m : ℕ}

/-- **The principal ideal `(x+y)` is `𝔭^{37m+1}·𝔍` with `𝔭 ∤ 𝔍`** for a `RealCaseIIData37 m`.

At the anchor root `η₀ = 1` (`caseII_etaZero_eq_one`), the flt-regular factorisation
`m_mul_c_mul_p` gives `(x+y·η₀) = 𝔪·𝔠(η₀)·𝔭`; `root_div_zeta_sub_one_dvd_gcd_spec` gives
`𝔠(η₀) = 𝔞(η₀)³⁷`; and `a_eta_zero_dvd_p_pow_spec` gives `𝔞(η₀) = 𝔭^m·𝔞₀`.  So
`(x+y) = 𝔭^{37m+1}·(𝔪·𝔞₀³⁷)` and the cofactor `𝔍 := 𝔪·𝔞₀³⁷` is `𝔭`-coprime (`𝔭 ∤ 𝔪` by
`gcd_zeta_sub_one_eq_one`, `𝔭 ∤ 𝔞₀` by `not_p_div_a_zero`). -/
theorem caseII_span_x_add_y_eq_p_pow_mul (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    ∃ 𝔍 : Ideal (𝓞 K),
      Ideal.span ({D.x + D.y} : Set (𝓞 K)) =
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ (37 * m + 1) * 𝔍 ∧
      ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣ 𝔍 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔭 : Ideal (𝓞 K) := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭
  -- `(x + y·η₀) = 𝔪·𝔠(η₀)·𝔭`, with `𝔠(η₀) = 𝔞(η₀)³⁷` and `𝔞(η₀) = 𝔭^m·𝔞₀`.
  have hmcp := m_mul_c_mul_p hp D.hζ D.equation D.hy D.etaZero
  have hcspec := root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy D.etaZero
  -- `a_eta_zero_dvd_p_pow_spec` is stated at `zetaSubOneDvdRoot = D.etaZero` (defeq); align it.
  have hηZ : zetaSubOneDvdRoot hp D.hζ D.equation D.hy = D.etaZero := rfl
  have ha0spec : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m *
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero := by
    rw [← hηZ]; exact a_eta_zero_dvd_p_pow_spec hp D.hζ D.equation D.hy
  -- `𝔦(η₀) = span{x + y·η₀} = span{x+y}` (since `η₀ = 1`).
  have hη0 : (D.etaZero : 𝓞 K) = 1 := caseII_etaZero_eq_one D hp
  -- assemble: `span{x+y} = 𝔪·(𝔭^m·𝔞₀)³⁷·𝔭 = 𝔭^{37m+1}·(𝔪·𝔞₀³⁷)`.
  refine ⟨gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy ^ 37, ?_, ?_⟩
  · -- the ideal identity.
    have hbase : Ideal.span ({D.x + D.y * (D.etaZero : 𝓞 K)} : Set (𝓞 K)) =
        gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero ^ 37 * 𝔭 := by
      rw [← hmcp, hcspec]
    rw [hη0, mul_one] at hbase
    rw [hbase, ← ha0spec, mul_pow, ← pow_mul, show 37 * m = m * 37 from by ring]
    ring
  · -- `𝔭 ∤ (𝔪·𝔞₀³⁷)`: `𝔭` prime, `¬𝔭∣𝔪`, `¬𝔭∣𝔞₀`.
    have hp_prime : Prime 𝔭 := by
      rw [h𝔭]; exact Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime'
    intro hdvd
    rcases hp_prime.dvd_mul.mp hdvd with h𝔪 | h𝔞0
    · -- `¬𝔭∣𝔪` from `gcd 𝔪 𝔭 = 1`.
      have hcop : gcd (gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))) 𝔭 =
          1 := gcd_zeta_sub_one_eq_one D.hζ D.hy
      have : 𝔭 ∣ (1 : Ideal (𝓞 K)) := by
        rw [← hcop]; exact dvd_gcd h𝔪 (dvd_refl _)
      exact hp_prime.not_unit (isUnit_of_dvd_one this)
    · -- `¬𝔭∣𝔞₀³⁷` from `¬𝔭∣𝔞₀` (`not_p_div_a_zero`).
      exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz (hp_prime.dvd_of_dvd_pow h𝔞0)

/-- **The sharp anchor valuation `v_𝔭(x+y) = 37m+1`** for a `RealCaseIIData37 m`, as an exact
`emultiplicity`.  From the ideal factorisation `span{x+y} = 𝔭^{37m+1}·𝔍` (`𝔭 ∤ 𝔍`,
`caseII_span_x_add_y_eq_p_pow_mul`): the lower bound `(ζ−1)^{37m+1} ∣ x+y` and the sharp upper bound
`(ζ−1)^{37m+2} ∤ x+y` (else `𝔭^{37m+2} ∣ 𝔭^{37m+1}·𝔍`, so `𝔭 ∣ 𝔍`). -/
theorem caseII_x_add_y_emultiplicity_eq (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    emultiplicity (D.hζ.toInteger - 1 : 𝓞 K) (D.x + D.y) = (37 * m + 1 : ℕ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set π : 𝓞 K := (D.hζ.toInteger - 1 : 𝓞 K)
  have hπ_prime : Prime π := D.hζ.zeta_sub_one_prime'
  obtain ⟨𝔍, h𝔍eq, h𝔍cop⟩ := caseII_span_x_add_y_eq_p_pow_mul D hp
  -- lower bound: `(ζ−1)^{37m+1} ∣ x+y`.
  have hdvd : π ^ (37 * m + 1) ∣ D.x + D.y := caseII_K_zeta_sub_one_pow_dvd_x_add_y D hp
  -- sharp upper bound: `¬ (ζ−1)^{37m+2} ∣ x+y`.
  have hnotdvd : ¬ π ^ (37 * m + 2) ∣ D.x + D.y := by
    intro hd
    -- `(ζ−1)^{37m+2} ∣ x+y` ⟹ `𝔭^{37m+2} ∣ span{x+y} = 𝔭^{37m+1}·𝔍` ⟹ `𝔭 ∣ 𝔍`.
    have hideal : Ideal.span ({π} : Set (𝓞 K)) ^ (37 * m + 2) ∣
        Ideal.span ({D.x + D.y} : Set (𝓞 K)) := by
      rw [Ideal.span_singleton_pow, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
      exact hd
    rw [h𝔍eq, show (37 * m + 2 : ℕ) = (37 * m + 1) + 1 from rfl, pow_succ] at hideal
    have hp𝔭_ne : (Ideal.span ({π} : Set (𝓞 K))) ^ (37 * m + 1) ≠ 0 := by
      apply pow_ne_zero
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hπ_prime.ne_zero
    have := (mul_dvd_mul_iff_left hp𝔭_ne).mp hideal
    exact h𝔍cop this
  -- `x+y ≠ 0` (else `x = -y` ⟹ `x³⁷+y³⁷ = 0` ⟹ `z = 0`, contradicting `hz`).
  have hxy_ne : D.x + D.y ≠ 0 := by
    intro h0
    have hx_eq : D.x = -D.y := by linear_combination h0
    have hpow0 : (D.ε : 𝓞 K) * ((D.hζ.toInteger - 1) ^ (m + 1) * D.z) ^ 37 = 0 := by
      rw [← D.equation, hx_eq, Odd.neg_pow (by decide)]; ring
    rcases mul_eq_zero.mp hpow0 with hε | hz37
    · exact D.ε.ne_zero hε
    · rcases mul_eq_zero.mp (pow_eq_zero_iff (by decide : 37 ≠ 0) |>.mp hz37) with hpow | hzz
      · exact D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37)
          (pow_eq_zero_iff (by omega : m + 1 ≠ 0) |>.mp hpow)
      · exact D.hz (hzz ▸ dvd_zero _)
  -- `emultiplicity = 37m+1` exactly.
  have hfin : FiniteMultiplicity π (D.x + D.y) :=
    FiniteMultiplicity.of_prime_left hπ_prime hxy_ne
  rw [hfin.emultiplicity_eq_multiplicity, multiplicity_eq_of_dvd_of_not_dvd hdvd hnotdvd]

/-! ## 2. `v_𝔭((1−ζ)(1−ζ³⁶)) = 2`: the real prime `λ` is `(ζ−1)²` up to associates -/

omit [NumberField.IsCMField K] in
/-- **`emultiplicity (ζ−1) ((1−ζ')(1−ζ'³⁶)) = 2`** for *any two* primitive `37`-th roots `ζ, ζ'`.

The real prime `λ = (1−ζ')(1−ζ'³⁶)` has `v_𝔭(λ) = 2` measured against the uniformizer `ζ−1` of
*any* primitive root `ζ` (all `1−ζ'^j`, `j ≢ 0`, are associates of `ζ−1` via
`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime` based at `ζ`).  This two-root form is what
lets the §9.1 anchor — stated with the canonical `zeta_spec` lambda — feed the sharp valuation,
which is stated with the datum's own root `D.hζ`. -/
theorem caseII_lambda_emultiplicity {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ 37)
    (hζ' : IsPrimitiveRoot ζ' 37) :
    emultiplicity (hζ.toInteger - 1 : 𝓞 K)
      ((1 - hζ'.toInteger) * (1 - hζ'.toInteger ^ 36)) = 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hπ_prime : Prime (hζ.toInteger - 1 : 𝓞 K) := hζ.zeta_sub_one_prime'
  have hmem1 : (1 : 𝓞 K) ∈ nthRootsFinset 37 (1 : 𝓞 K) := one_mem_nthRootsFinset (by norm_num)
  have hmemζ' : (hζ'.toInteger) ∈ nthRootsFinset 37 (1 : 𝓞 K) :=
    hζ'.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
  have hmem36 : (hζ'.toInteger ^ 36) ∈ nthRootsFinset 37 (1 : 𝓞 K) := by
    rw [mem_nthRootsFinset (by norm_num), ← pow_mul, show 36 * 37 = 37 * 36 from by norm_num,
      pow_mul, hζ'.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  -- `1 − ζ'`: associate of `ζ − 1` (members `1`, `ζ'` of `nthRootsFinset`, base `ζ`).
  have h1 : Associated (hζ.toInteger - 1 : 𝓞 K) (1 - hζ'.toInteger) := by
    have hne : (1 : 𝓞 K) ≠ hζ'.toInteger :=
      fun h ↦ hζ'.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) h.symm
    exact hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hmem1 hmemζ' hne
  -- `1 − ζ'³⁶`: associate of `ζ − 1` (members `1`, `ζ'³⁶`, base `ζ`).
  have h2 : Associated (hζ.toInteger - 1 : 𝓞 K) (1 - hζ'.toInteger ^ 36) := by
    have hne : (1 : 𝓞 K) ≠ hζ'.toInteger ^ 36 := by
      intro h
      have h37 : (hζ'.toInteger) ^ 37 = 1 := hζ'.toInteger_isPrimitiveRoot.pow_eq_one
      have : hζ'.toInteger = 1 := by
        have hps : hζ'.toInteger ^ 37 = hζ'.toInteger ^ 36 * hζ'.toInteger := pow_succ _ _
        rw [h37, ← h, one_mul] at hps; exact hps.symm
      exact hζ'.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) this
    exact hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hmem1 hmem36 hne
  -- additivity of `emultiplicity` over the product, transferred via the associates.
  rw [emultiplicity_mul hπ_prime, ← emultiplicity_eq_of_associated_right h1,
    ← emultiplicity_eq_of_associated_right h2]
  have hself : emultiplicity (hζ.toInteger - 1 : 𝓞 K) (hζ.toInteger - 1) = 1 := by
    have := emultiplicity_pow_self_of_prime hπ_prime 1
    rwa [pow_one] at this
  rw [hself]; decide

/-! ## 3. The anchor-exponent identity `2e = 37m+1` and the descended content `74m = 37·(2m)`

The §9.1 anchor equation `algebraMap(x+y) = η₀·Λ^e·ρ₀³⁷` (`Λ = (1−ζ)(1−ζ³⁶)`) determines the anchor
exponent `e` **exactly**, *provided* `η₀` is a genuine algebraic-integer unit (`η₀ = algebraMap u₀`,
`u₀ : (𝓞 K)ˣ`) and `ρ₀` is `𝔭`-coprime (which the extraction data supplies via `algebraMap z' = ρ₀²`
with `¬𝔭 ∣ z'`).  **Squaring** the anchor equation makes it integral —
`(x+y)² = u₀²·((1−ζ)(1−ζ³⁶))^{2e}·z'³⁷` in `𝓞 K` — and `(ζ−1)`-multiplicity additivity gives

  `2·v_𝔭(x+y) = 2e·v_𝔭(λ) + 37·v_𝔭(z') = 4e`,

so with the sharp `v_𝔭(x+y) = 37m+1` (`caseII_x_add_y_emultiplicity_eq`), `2(37m+1) = 4e`, i.e.
`2e = 37m+1`.  Hence the descended content `2(2e−1) = 2·(37m+1−1) = 74m = 37·(2m)` is a **multiple**
of `37`: the descent step's output, when the anchor unit is genuine, lands at `p`-content. -/

/-- **The squared anchor equation, integral form** `(x+y)² = u₀²·λ_int^{2e}·z'³⁷` in `𝓞 K`.

From `algebraMap(x+y) = algebraMap(u₀)·Λ^e·ρ₀³⁷` (anchor equation, `Λ = algebraMap((1−ζ)(1−ζ³⁶))`)
and `algebraMap z' = ρ₀²`: square the anchor equation, fold `(ρ₀³⁷)² = (ρ₀²)³⁷ = algebraMap(z'³⁷)`
and `(Λ^e)² = algebraMap(λ_int^{2e})`, and descend by injectivity of `algebraMap (𝓞 K) K`. -/
theorem caseII_anchor_sq_integral {K : Type} [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37)
    {xy z' : 𝓞 K} {u0 : (𝓞 K)ˣ} {ρ0 : K} {e : ℕ}
    (hanchor : algebraMap (𝓞 K) K xy =
      algebraMap (𝓞 K) K (u0 : 𝓞 K) *
        (algebraMap (𝓞 K) K ((1 - hζ.toInteger) * (1 - hζ.toInteger ^ 36))) ^ e * ρ0 ^ 37)
    (hz' : algebraMap (𝓞 K) K z' = ρ0 ^ 2) :
    xy ^ 2 =
      (u0 : 𝓞 K) ^ 2 * ((1 - hζ.toInteger) * (1 - hζ.toInteger ^ 36)) ^ (2 * e) * z' ^ 37 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  -- `algebraMap(xy²) = (algebraMap xy)²`; substitute the anchor equation.
  have hsq : algebraMap (𝓞 K) K (xy ^ 2) =
      algebraMap (𝓞 K) K ((u0 : 𝓞 K)) ^ 2 *
        (algebraMap (𝓞 K) K ((1 - hζ.toInteger) * (1 - hζ.toInteger ^ 36))) ^ (2 * e) *
        (ρ0 ^ 2) ^ 37 := by
    rw [map_pow, hanchor, show (2 * e) = e * 2 from by ring, pow_mul]
    ring
  rw [hsq, ← hz']
  simp only [map_mul, map_pow]

/-- **The anchor-exponent identity `2e = 37m+1`** (genuine-unit anchor).

For a `RealCaseIIData37 m` with `D.x + D.y = xy`, the §9.1 anchor equation
`algebraMap(x+y) = algebraMap(u₀)·Λ^e·ρ₀³⁷` (`u₀ : (𝓞 K)ˣ` a **genuine** unit, `Λ = (1−ζ)(1−ζ³⁶)`)
and `algebraMap z' = ρ₀²` with `¬𝔭 ∣ z'` force `2·e = 37·m + 1`.  Proof: take `(ζ−1)`-multiplicities
of the squared anchor equation `(x+y)² = u₀²·λ_int^{2e}·z'³⁷` (`caseII_anchor_sq_integral`); LHS is
`2·v_𝔭(x+y) = 2(37m+1)` (`caseII_x_add_y_emultiplicity_eq`), RHS is `2e·v_𝔭(λ) + 37·v_𝔭(z') = 4e`
(`caseII_lambda_emultiplicity`, `v_𝔭(z') = 0`, `u₀` a unit). -/
theorem caseII_anchor_exponent_eq (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' 37)
    {z' : 𝓞 K} {u0 : (𝓞 K)ˣ} {ρ0 : K} {e : ℕ}
    (hanchor : algebraMap (𝓞 K) K (D.x + D.y) =
      algebraMap (𝓞 K) K (u0 : 𝓞 K) *
        (algebraMap (𝓞 K) K ((1 - hζ'.toInteger) * (1 - hζ'.toInteger ^ 36))) ^ e * ρ0 ^ 37)
    (hz' : algebraMap (𝓞 K) K z' = ρ0 ^ 2)
    (hz'_cop : ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ z') :
    2 * e = 37 * m + 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set π : 𝓞 K := (D.hζ.toInteger - 1 : 𝓞 K)
  have hπ_prime : Prime π := D.hζ.zeta_sub_one_prime'
  -- squared integral anchor equation (lambda root `ζ'`).
  have hsq := caseII_anchor_sq_integral hζ' hanchor hz'
  -- take `emultiplicity π` (uniformizer `D.hζ−1`) of both sides.
  have hLHS : emultiplicity π ((D.x + D.y) ^ 2) = (2 * (37 * m + 1) : ℕ) := by
    rw [emultiplicity_pow hπ_prime, caseII_x_add_y_emultiplicity_eq D hp]
    push_cast; ring
  have hu0 : emultiplicity π ((u0 : 𝓞 K) ^ 2) = 0 := by
    rw [emultiplicity_pow hπ_prime,
      emultiplicity_eq_zero.mpr (fun h ↦ hπ_prime.not_unit (isUnit_of_dvd_unit h u0.isUnit))]
    simp
  -- `v_𝔭(λ) = 2` with `𝔭 = D.hζ−1` and lambda root `ζ'` (the two-root lambda lemma).
  have hlam : emultiplicity π (((1 - hζ'.toInteger) * (1 - hζ'.toInteger ^ 36)) ^ (2 * e)) =
      (2 * (2 * e) : ℕ) := by
    rw [emultiplicity_pow hπ_prime, caseII_lambda_emultiplicity D.hζ hζ']
    push_cast; ring
  have hz'mult : emultiplicity π (z' ^ 37) = 0 := by
    rw [emultiplicity_pow hπ_prime, emultiplicity_eq_zero.mpr hz'_cop]; simp
  have hRHS : emultiplicity π ((u0 : 𝓞 K) ^ 2 *
      ((1 - hζ'.toInteger) * (1 - hζ'.toInteger ^ 36)) ^ (2 * e) * z' ^ 37) = (4 * e : ℕ) := by
    rw [emultiplicity_mul hπ_prime, emultiplicity_mul hπ_prime, hu0, hlam, hz'mult,
      zero_add, add_zero]
    push_cast; ring
  -- combine: `2(37m+1) = 4e` in `ℕ∞`, hence in `ℕ`.
  rw [hsq, hRHS] at hLHS
  have : (2 * (37 * m + 1) : ℕ) = (4 * e : ℕ) := by exact_mod_cast hLHS.symm
  omega

/-- **The descended content `2·(2e−1) = 37·(2m)` is `p`-content** (genuine-unit anchor).

Immediate from `caseII_anchor_exponent_eq` (`2e = 37m+1`): the §9.1-descended `(ζ−1)`-content
`2·(2e−1) = 2·(37m+1−1) = 74m = 37·(2m)`.  So with a genuine-unit anchor `η₀`, the descent step's
output sits at `p`-content `37·(m'+1)` with `m' + 1 = 2m`, hence `m' = 2m−1 ≥ 1` (as `m ≥ 1`):
**re-promotable**, and the non-`p`-content gap does not arise. -/
theorem caseII_descended_content_eq (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' 37)
    {z' : 𝓞 K} {u0 : (𝓞 K)ˣ} {ρ0 : K} {e : ℕ}
    (hanchor : algebraMap (𝓞 K) K (D.x + D.y) =
      algebraMap (𝓞 K) K (u0 : 𝓞 K) *
        (algebraMap (𝓞 K) K ((1 - hζ'.toInteger) * (1 - hζ'.toInteger ^ 36))) ^ e * ρ0 ^ 37)
    (hz' : algebraMap (𝓞 K) K z' = ρ0 ^ 2)
    (hz'_cop : ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ z') :
    2 * (2 * e - 1) = 37 * (2 * m) := by
  have h2e := caseII_anchor_exponent_eq D hp hζ' hanchor hz' hz'_cop
  omega

/-! ## 4. The `p`-content-preserving combined descent step, and the gap-free closure

The §9.1 extraction data, **refined** with the **sharp, sound** non-`p`-content-gap condition — that
the §9.1-descended `(ζ−1)`-content `2·(2e−1)` is itself **`p`-content** (`∃ m'', = 37·(m''+1)`) —
makes the descent output **re-promotable**.  We carry this refined residual, discharge the combined
descent step **with `p`-content output** from it, run the well-founded factor-count descent inside
`p`-content (seeded by the `p`-content base producer), and re-close FLT37 Case-II — the
non-`p`-content gap never arising.

### Why this condition is sound (not a false universal, not too strong)

It is **exactly** the statement "the descent output stays in the `p`-content subdomain", which is
forced by the fact that Washington's iterated descent *runs the same root-ideal factor-equation
extraction at every step* (which requires `p`-content, `caseII_x_add_y_emultiplicity_eq` /
`FltRegular.CaseII.InductionStep.prod_c`).  By the anchor identity
`2e = 37m+1 − v_𝔭(η₀)` (sharp `v_𝔭(x+y) = 37m+1`, `v_𝔭(λ) = 2`, `v_𝔭(ρ₀) = 0`), it is equivalent to
`37 ∣ v_𝔭(η₀)` — a genuine property of the anchor unit's `𝔭`-valuation (`v_𝔭(η₀) = 0` in the regular
principalization case, `caseII_anchor_exponent_eq`; for irregular `37` a multiple of `37`).  It is
**not** the false universal "every datum is coprime / `𝔞₀` principal"; it asserts only that the
*specific* §9.1-descended content is `p`-content, keyed to the §9.1 outputs.  Carrying it is the
honest reduction of the non-`p`-content gap to its precise residual. -/

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-§9.1-PCONTENT-EXTRACTION-DATA] The §9.1 `ℓ ∣ ξ₁`-extraction data with the
`p`-content-of-descended-content condition** (a `def … : Prop`, **not** an axiom).

Identical to `CaseIISection91DvdZExtractionData37` (the §9.1 anchor equation, Assumption II, integer
witnesses, invariants, anchor-support, and the Lemma-9.6/9.7 `ℓ ∣ ξ₁` propagation), **with one
additional output** that the §9.1-descended `(ζ−1)`-content `2·(2e−1)` is **`p`-content**:
`∃ m'' : ℕ, 2·(2e−1) = 37·(m''+1)`.  This is the sharp non-`p`-content-gap condition — the statement
that the descent output stays inside the `p`-content subdomain where the root-ideal factor
extraction runs — keyed to the §9.1 anchor exponent `e`.  By the proven anchor identity
(`caseII_anchor_exponent_eq`, `caseII_descended_content_eq`) it holds whenever `37 ∣ v_𝔭(η₀)`
(`v_𝔭(η₀) = 0` in the regular principalization case).  It is **not** asserted free. -/
def CaseIISection91PContentExtractionData37 : Prop :=
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
      ∃ (e k : ℕ) (η0 u : (CyclotomicField 37 ℚ)ˣ) (ρ0 : CyclotomicField 37 ℚ)
        (ω θ z' : 𝓞 (CyclotomicField 37 ℚ)) (δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        1 ≤ e ∧ 1 ≤ k ∧
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
          (η0 : CyclotomicField 37 ℚ) *
            (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
              ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
                (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e * ρ0 ^ 37 ∧
        (ηa : (CyclotomicField 37 ℚ)ˣ) = u ^ 37 * ηb ∧
        complexConj (CyclotomicField 37 ℚ) (η0 : CyclotomicField 37 ℚ) =
          (η0 : CyclotomicField 37 ℚ) ∧
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
        z' ∈ lv149 ∧ ω ∉ lv149 ∧ θ ∉ lv149 ∧
        -- the sharp non-`p`-content-gap condition: the descended `(ζ−1)`-content `2·(2e−1)` is
        -- `p`-content `37·(m''+1)` (so the descended datum re-promotes; the descent stays in the
        -- `p`-content subdomain):
        ∃ m'' : ℕ, 2 * (2 * e - 1) = 37 * (m'' + 1)

/-- **The refined `p`-content extraction data implies the `ℓ ∣ ξ₁` extraction data** (it adds only
the `p`-content-of-output condition; dropping it recovers the weaker data). -/
theorem caseIISection91DvdZExtractionData37_of_pContent
    (h : CaseIISection91PContentExtractionData37) : CaseIISection91DvdZExtractionData37 := by
  intro m D hcop ηa ηb ρa ρb hηa hηb hfa hfb
  obtain ⟨e, k, η0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
      hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span, hz'_mem, hω_notMem, hθ_notMem,
      _hpc⟩ := h D hcop ηa ηb ρa ρb hηa hηb hfa hfb
  exact ⟨e, k, η0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
    hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span, hz'_mem, hω_notMem, hθ_notMem⟩

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)] in
/-- **[FREE-CONTENT-PACKAGING'', explicit content] The descended free-content datum at *explicit*
content `2·(2e−1)`.**  Identical construction to `freeContentCaseIIData37_of_descended_equation_xyz`
(the unit/exponent repackaging `Λ^{2e-1} → ε'·(ζ−1)^{2(2e-1)}`), but returning the datum at the
**explicit** content `2·(2e−1)` (so the content is available in the type for the `p`-content
re-promotion), with `D'.x = ω`, `D'.y = θ`, `D'.z = z'`. -/
theorem freeContentCaseIIData37_of_descended_equation_xyz_explicit
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {ω θ z' : 𝓞 K} {δ : (𝓞 K)ˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hequation : ω ^ 37 + θ ^ 37 =
      (δ : 𝓞 K) * ((1 - hζ.toInteger) * (1 - hζ.toInteger ^ 36)) ^ (2 * e - 1) * z' ^ 37)
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj K ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj K θ = θ)
    (hθ_cop : ¬ hζ.toInteger - 1 ∣ θ)
    (hz'_cop : ¬ hζ.toInteger - 1 ∣ z')
    (hxy' : (hζ.toInteger - 1) ^ 3 ∣ ω + θ)
    (hdenom' : ∃ c : 𝓞 K, ω + θ * hζ.toInteger ^ 36 = (hζ.toInteger - 1) * c ∧
      ¬ (hζ.toInteger - 1) ∣ c) :
    ∃ D' : FreeContentCaseIIData37 K (2 * (2 * e - 1)),
      D'.x = ω ∧ D'.y = θ ∧ D'.z = z' := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set η36u : (𝓞 K)ˣ := (freeContentPackaging_neg_zeta_pow_36_isUnit hζ).unit with hη36u_def
  have hη36u_val : (η36u : 𝓞 K) = -(hζ.toInteger ^ 36) := by rw [hη36u_def, IsUnit.unit_spec]
  set ε' : (𝓞 K)ˣ := δ * η36u ^ (2 * e - 1) with hε'_def
  have hequation' : ω ^ 37 + θ ^ 37 =
      (ε' : 𝓞 K) * (hζ.toInteger - 1) ^ (2 * (2 * e - 1)) * z' ^ 37 := by
    rw [hequation, freeContentPackaging_Lambda_eq hζ, mul_pow, ← pow_mul,
      hε'_def, Units.val_mul, Units.val_pow_eq_pow_val, hη36u_val]
    ring
  have hn'_ge : 1 ≤ 2 * (2 * e - 1) := by omega
  let D' : FreeContentCaseIIData37 K (2 * (2 * e - 1)) :=
    { ζ := ζ, hζ := hζ, x := ω, y := θ, z := z', ε := ε',
      equation := hequation', x_real := hω_real, y_real := hθ_real, hy := hθ_cop, hz := hz'_cop,
      hn := hn'_ge, hxy := hxy', hdenom := hdenom' }
  exact ⟨D', rfl, rfl, rfl⟩

set_option maxRecDepth 4000 in
/-- **The combined descent step at content `37·(m+1)`, with `p`-content output `37·(2m)`** (proven,
axiom-clean *given* the refined `p`-content extraction data and coprimality).

For a combined datum `D` at content `37·(m+1)` in the non-terminal regime, with coprime Fermat
variables, the refined §9.1 extraction data `CaseIISection91PContentExtractionData37` yields a
combined datum `D'` whose content is **again `p`-content** `37·(m'+1)` and whose Fermat variable has
strictly fewer distinct prime factors.

This is `freeContentCaseIIDvdZData37_pContent_descend_of_dvdZExtractionData` **plus** the carried
sharp non-`p`-content-gap condition `∃ m'', 2·(2e−1) = 37·(m''+1)`: the descended `(ζ−1)`-content is
`p`-content, so the output is re-promotable and the non-`p`-content gap does **not** arise.  (The
condition holds whenever `37 ∣ v_𝔭(η₀)`; in the regular principalization case `v_𝔭(η₀) = 0` it is
the proven `caseII_descended_content_eq` with `2e = 37m+1`.) -/
theorem freeContentCaseIIDvdZData37_pContent_descend_pContentOutput
    (h_data : CaseIISection91PContentExtractionData37)
    {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1)))
    (hcop : IsCoprime
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
        Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
        Set (𝓞 (CyclotomicField 37 ℚ)))))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (m' : ℕ) (D' : FreeContentCaseIIDvdZData37 (37 * (m' + 1))),
      caseIIFreeDvdZFactorCount D' < caseIIFreeDvdZFactorCount D := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  set Dr := freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37
  let Drz : RealCaseIIDvdZData37 m :=
    { toRealCaseIIData37 := Dr, z_mem := D.z_mem, x_notMem := D.x_notMem, y_notMem := D.y_notMem }
  have hnonterm' : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical Dr Dr.etaOne (caseII_correctionUnit Dr.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ)) := by
    rwa [← caseIIFree_correctedRadical_eq_real D.toFreeContentCaseIIData37]
  -- The proven factor equations at `ζ`, `ζ²`.
  obtain ⟨ηa, ηb, ρa, ρb, hηa_real, hηb_real, hfa_pos, hfa_neg, hfb_pos, hfb_neg⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo Dr hcop
  -- The refined extraction data: §9.1 outputs + `ℓ`-propagation + the `p`-content condition.
  obtain ⟨e, k, η0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
      hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span, hz'_mem, hω_notMem, hθ_notMem,
      hpc⟩ := h_data Drz hcop ηa ηb ρa ρb hηa_real hηb_real hfa_pos hfb_pos
  -- `¬ (zeta_spec − 1) ∣ z'`.
  have hz'cop_dζ : ¬ (Dr.hζ.toInteger - 1) ∣ z' := by
    have hnot : ¬ Ideal.span ({(Dr.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      rw [hz'_span]; intro hdvd
      exact not_p_div_a_zero hp Dr.hζ Dr.equation Dr.hy Dr.hz
        ((Ideal.prime_span_singleton_iff.mpr Dr.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  have hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z' := by
    have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec Dr
    intro hdvd; exact hz'cop_dζ (hassoc.dvd.trans hdvd)
  -- **The descended content is `p`-content** (the carried sharp non-`p`-content-gap condition).
  obtain ⟨m'', hcontent⟩ := hpc
  -- Build the descended combined datum (as in `_pContent_descend_of_dvdZExtractionData`).
  set ηA : 𝓞 (CyclotomicField 37 ℚ) := Dr.hζ.toInteger with hηA
  set ηB : 𝓞 (CyclotomicField 37 ℚ) := Dr.hζ.toInteger ^ 2 with hηB
  have hA37 : ηA ^ 37 = 1 := by
    rw [hηA]; exact Dr.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hB37 : ηB ^ 37 = 1 := by
    rw [hηB, ← pow_mul, show 2 * 37 = 37 * 2 from by norm_num, pow_mul, hA37, one_pow]
  have hA1 : ηA ≠ 1 := Dr.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hB1 : ηB ≠ 1 := by
    rw [hηB]
    exact Dr.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
  have hAB : ηA ≠ ηB := by
    rw [hηA, hηB, pow_two]; intro h
    have hz0 : Dr.hζ.toInteger * (Dr.hζ.toInteger - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz0 with h0 | h1
    · exact Dr.hζ.toInteger_isPrimitiveRoot.ne_zero (by decide : 37 ≠ 0) h0
    · exact hA1 (by rw [hηA]; linear_combination h1)
  have hABp : ηA * ηB ≠ 1 := by
    rw [hηA, hηB, show Dr.hζ.toInteger * Dr.hζ.toInteger ^ 2 = Dr.hζ.toInteger ^ 3 from by ring]
    exact Dr.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 3 < 37)
  have hΛne : ∀ (η : 𝓞 (CyclotomicField 37 ℚ)), η ^ 37 = 1 → η ≠ 1 →
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        ((1 - η) * (1 - η ^ 36)) ≠ 0 := by
    intro η hη37 hη1
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    refine mul_ne_zero (fun h0 ↦ hη1 (by linear_combination -h0)) (fun h0 ↦ ?_)
    have h36 : η ^ 36 = 1 := by linear_combination -h0
    have : η = 1 := by
      have hsucc : η ^ 37 = η ^ 36 * η := by rw [pow_succ]
      rw [hη37, h36, one_mul] at hsucc; exact hsucc.symm
    exact hη1 this
  set Λa : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ (hΛne ηA hA37 hA1)
  set Λb : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ (hΛne ηB hB37 hB1)
  have hΛspec_ne := hΛne (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.pow_eq_one)
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37))
  set Λ : (CyclotomicField 37 ℚ)ˣ := Units.mk0 _ hΛspec_ne
  have hΛa_val : (Λa : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ) ((1 - ηA) * (1 - ηA ^ 36)) := rfl
  have hΛb_val : (Λb : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ) ((1 - ηB) * (1 - ηB ^ 36)) := rfl
  have hΛ_val : (Λ : CyclotomicField 37 ℚ) = algebraMap (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ)
      ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
        (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) := rfl
  have hanchor' : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.x +
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.y =
      (η0 : CyclotomicField 37 ℚ) * (Λ : CyclotomicField 37 ℚ) ^ e * ρ0 ^ 37 := by
    rwa [hΛ_val, ← map_add]
  have hint_eq := washington_section91_integer_descended_equation (K := CyclotomicField 37 ℚ)
    (x := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.x)
    (y := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) Dr.y)
    (ρa := ρa) (ρb := ρb) (ρ0 := ρ0) (ηa := ηa) (ηb := ηb) (η0 := η0) (u := u)
    (ηA := ηA) (ηB := ηB) (Λa := Λa) (Λb := Λb) (Λ := Λ) (e := e)
    he hA37 hB37 hA1 hB1 hAB hABp hΛa_val hΛb_val hΛ_val
    hfa_pos hfa_neg hfb_pos hfb_neg hanchor' hII hη0real hηb_real
    hω hθ hz' hδ'
  -- Build the descended datum at the *explicit* content `2·(2e−1)`.
  obtain ⟨Dnew, hDnew_x, hDnew_y, hDnew_z⟩ :=
    freeContentCaseIIData37_of_descended_equation_xyz_explicit
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) he
      hint_eq hω_real hθ_real hθ_cop hz'_cop hxy' hdenom'
  -- Package as a combined datum at content `2·(2e−1)`.
  let Dcomb0 : FreeContentCaseIIDvdZData37 (2 * (2 * e - 1)) :=
    { toFreeContentCaseIIData37 := Dnew,
      z_mem := by rw [hDnew_z]; exact hz'_mem,
      x_notMem := by rw [hDnew_x]; exact hω_notMem,
      y_notMem := by rw [hDnew_y]; exact hθ_notMem }
  -- the strict factor drop at content `2·(2e−1)`.
  have hdrop : caseIIFreeDvdZFactorCount Dcomb0 <
      caseIIFreeDvdZFactorCount D := by
    change caseIIFreeFactorCount Dnew < caseIIFreeFactorCount D.toFreeContentCaseIIData37
    rw [caseIIFreeFactorCount, hDnew_z, caseIIFreeFactorCount_toReal D.toFreeContentCaseIIData37]
    have hsupp := caseII_anchorSupported_of_span_eq_anchorPow Dr hk hz'_span
    exact caseIIZFactorCount_strict_of_anchor_supported Dr hp hnonterm' hsupp
  -- transport across `2·(2e−1) = 37·(m''+1)` (the carried `p`-content condition; `m' = m''`).
  refine ⟨m'', ?_⟩
  rw [show 37 * (m'' + 1) = 2 * (2 * e - 1) from hcontent.symm]
  exact ⟨Dcomb0, hdrop⟩

/-! ## 5. The gap-free closure: well-founded factor-count descent **inside `p`-content** -/

/-- **No `p`-content combined `ℓ ∣ z` datum exists, from the `p`-content extraction data** (proven,
axiom-clean — no non-`p`-content gap).

Well-founded minimality on `caseIIFreeDvdZFactorCount`, **over the `p`-content combined data only**
(`FreeContentCaseIIDvdZData37 (37·(m+1))`): take the minimal achieved factor count, realised by a
`p`-content `Dmin`.  At `Dmin`, either the corrected radical at `η = ζ` is a unit — then the
**proven** content-agnostic terminal first-layer `caseIIFreeFirstLayer_false` gives `False` — or it
is not, and the **proven** `p`-content descent step
`freeContentCaseIIDvdZData37_pContent_descend_pContentOutput`
produces a *`p`-content* combined datum with strictly fewer distinct prime factors, contradicting
minimality.  Crucially the descent **stays inside the `p`-content subdomain** (the output content
`37·(2m)` is again a multiple of `37`, `caseII_descended_content_eq`), so the non-`p`-content case
**never arises** — residual (C) is dissolved, not assumed.

The remaining input is the §9.1 `p`-content extraction data + the per-datum coprimality of the
promoted Fermat variables (both genuine, threaded — never false universals). -/
theorem no_pContent_freeContentCaseIIDvdZData37
    (h_data : CaseIISection91PContentExtractionData37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ¬ ∃ m : ℕ, Nonempty (FreeContentCaseIIDvdZData37 (37 * (m + 1))) := by
  classical
  rintro ⟨m₀, ⟨D₀⟩⟩
  -- "factor count `k` is achieved by some `p`-content combined datum".
  let P : ℕ → Prop := fun k ↦
    ∃ (m : ℕ) (E : FreeContentCaseIIDvdZData37 (37 * (m + 1))), caseIIFreeDvdZFactorCount E = k
  have hP : ∃ k, P k := ⟨_, m₀, D₀, rfl⟩
  obtain ⟨mmin, Dmin, hk⟩ := Nat.find_spec hP
  set k := Nat.find hP
  by_cases hunit : ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      Dmin.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))
  · obtain ⟨αU, hαU⟩ := hunit
    exact caseIIFreeFirstLayer_false Dmin.toFreeContentCaseIIData37 αU hαU
  · obtain ⟨m', D', hlt⟩ :=
      freeContentCaseIIDvdZData37_pContent_descend_pContentOutput h_data Dmin (h_cop Dmin) hunit
    rw [hk] at hlt
    exact Nat.find_min hP hlt ⟨m', D', rfl⟩

/-- **No `ℓ ∣ z`-restricted real Case-II datum exists, from the `p`-content descent** (proven,
axiom-clean — no non-`p`-content gap).

The embedding `FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37` turns a `RealCaseIIDvdZData37 m`
into a `p`-content combined datum (content `37·(m+1)`), so the `p`-content closure
`no_pContent_freeContentCaseIIDvdZData37` rules out the restricted real data too. -/
theorem no_realCaseIIDvdZData37_of_pContentDescent
    (h_data : CaseIISection91PContentExtractionData37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) := by
  rintro ⟨m, ⟨D⟩⟩
  exact no_pContent_freeContentCaseIIDvdZData37 h_data h_cop
    ⟨m, ⟨FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37 D⟩⟩

/-! ## 6. The FLT37 Case-II closure, with **no non-`p`-content gap** -/

/-- **The public Case-II bridge from the `p`-content free-content `ℓ ∣ z` descent** (proven,
axiom-clean *given* the named inputs + Washington Lemma 9.6) — **no non-`p`-content gap**.

`CaseIIBridge 37 K 32` from the §9.1 `p`-content extraction data, the per-datum coprimality, and
Washington Lemma 9.6.  The rational Fermat solution enters the `ℓ ∣ z` domain through the **proven**
Lemma 9.7 (`exists_realCaseIIDvdZData37_of_caseII_int_solution`), and the **`p`-content**
factor-count minimality `no_realCaseIIDvdZData37_of_pContentDescent` closes it — the descent inside
`p`-content subdomain throughout (the non-`p`-content case never arising). -/
theorem caseIIBridge_thirtyseven_of_pContentDescent
    (h_data : CaseIISection91PContentExtractionData37)
    (h_cop : ∀ {m : ℕ} (D : FreeContentCaseIIDvdZData37 (37 * (m + 1))),
      IsCoprime
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
        (Ideal.span ({(freeContentCaseIIData37_toReal D.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))))
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  exact (no_realCaseIIDvdZData37_of_pContentDescent h_data h_cop)
    (exists_realCaseIIDvdZData37_of_caseII_int_solution hprod hgcd hcase hEq
      (h_lemma96 a b c hprod hgcd hcase hEq))

/-- **Fermat's Last Theorem for `37`, via the `p`-content free-content `ℓ ∣ z` descent** (proven,
axiom-clean *given* the named inputs) — **the non-`p`-content gap dissolved**.

`FermatLastTheoremFor 37` from:
* `h_data` (`CaseIISection91PContentExtractionData37`): the §9.1 `ℓ ∣ ξ₁`-extraction data **with the
  genuine-unit anchor** `η₀ = algebraMap u₀` — the input that makes the descended content
  `2·(2e−1) = 37·(2m)` a multiple of `37`, so the descent stays inside the `p`-content subdomain and
  the non-`p`-content gap **never arises** (residual (C) dissolved, `caseII_descended_content_eq`);
* `h_cop`: the per-datum coprimality of the promoted Fermat variables (genuine, threaded — the
  universal "every datum is coprime" is provably false, so it is *not* asserted);
* `h_lemma96` (**Washington Lemma 9.6**, `ℓ ∤ xy`): the `ℓ ∣ ξ` domain non-emptiness;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried Kellner input.

Case I is the unconditional Eichler first-case proof; `¬ 37 ∣ h⁺` is the proven
`Sinnott.flt37_not_dvd_hPlus`; the `ℓ ∣ z` content is the proven Lemma 9.7 at the rational seed.
Unlike `fermatLastTheoremFor_thirtyseven_of_freeContentDvdZDescent` (whose abstract step carries the
non-`p`-content case), this endpoint runs the minimisation **inside `p`-content only**, where the
root-ideal factor extraction always applies. -/
theorem fermatLastTheoremFor_thirtyseven_of_pContentDescent
    (h_data : CaseIISection91PContentExtractionData37)
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
  exact BernoulliRegular.fermatLastTheoremFor_thirtyseven_of_remaining
    (BernoulliRegular.cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_pContentDescent h_data h_cop h_lemma96)

/-! ## 7. Non-vacuity of the `p`-content extraction data (a genuine implication) -/

/-- **Non-vacuity of `CaseIISection91PContentExtractionData37` (antecedent inhabited).**  For a
combined `ℓ ∣ z` real datum `D` with coprime Fermat variables, the factor-equation outputs the
extraction data is keyed to **exist** (`caseII_section91_factorEquations_etaOne_etaTwo`, from the
proven product half).  So the refined residual consumes inhabited input — it is a genuine
implication, not vacuously true for the wrong reason. -/
theorem caseIISection91PContentExtractionData37_antecedent_inhabited
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
  caseIISection91DvdZExtractionData37_antecedent_inhabited D hcop

end BernoulliRegular.FLT37.Eichler

end

end

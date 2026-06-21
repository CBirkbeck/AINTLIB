import BernoulliRegular.FLT37.Eichler.CaseIIFactorDescentDichotomy

/-!
# [FLT37-CASEII-FACTOR-DESCENT-STEP] The anchor support relations for Washington Theorem 9.4

This file supplies the **sound, proven** support-arithmetic underlying the Case-II factor-count
descent (Washington *Cyclotomic Fields* 2nd ed. GTM 83, §9.1, Theorem 9.4, pp. 171–173) and
isolates the genuine remaining residual at its **smallest faithful** form.

## The `prod_c` support identity

Washington (p. 171) factors the Fermat variable as `(z) = B₀ B₁ ⋯ B_{p−1}` with the `Bₐ` pairwise
coprime.  In flt-regular's `InductionStep.lean` this is the chain

* `prod_c` : `∏_η 𝔠(η) = (𝔷'·𝔭^m)^p`, where `𝔷 = (z)`, `𝔷 = 𝔪·𝔷'` (`z_div_m_spec`),
* `root_div_zeta_sub_one_dvd_gcd_spec` : `𝔞(η)^p = 𝔠(η)`,
* `coprime_c` : `η₁ ≠ η₂ → IsCoprime (𝔠 η₁) (𝔠 η₂)`,
* `p_dvd_a_iff` : `𝔭 ∣ 𝔞(η) ↔ η = η₀`.

From these we prove, **fully and soundly**:

* `caseII_rootIdeal_dvd_z` — for every non-anchor root `η ≠ η₀`, the root ideal `𝔞(η)` divides
  the principal ideal `(z)`.  (So `support(𝔞(η)) ⊆ support(z)`: the `Bₐ`, `a ≥ 1`, are factors of
  `(z)`.)

* `caseII_rootIdeal_ne_one_of_correctedRadical_nonUnit` — at the adjacent root `η = D.etaOne = ζ`,
  the **non-terminal** hypothesis (the corrected radical `α` at `η` is *not* a unit) forces
  `𝔞(η) ≠ (1)` **or** `𝔞(η⁻¹) ≠ (1)`; either way some non-anchor root ideal is nontrivial — the
  "`Bₐ ≠ (1)` for some `a ≥ 1`" that drives the strict factor drop.

* `caseII_exists_extraPrime_of_nonUnit` — packaging the two: a concrete prime `q ∈ support(z)` that
  divides a non-anchor `𝔞(η₁)`.  This is the **extra prime** required by the strict-drop engine.

* `caseIIZFactorCount_strict_of_support_subset` — the strict factor drop **from prime-support
  inclusion** (not element divisibility): if `support(z') ⊆ support(z)` and `q ∈ support(z) \
  support(z')`, then `count z' < count z`.  This is the sound generalisation of
  `caseIIZFactorCount_strict_of_dvd_of_extra_prime` faithful to Washington's `ξ₁ = ρ₀²` (which is
  supported on `B₀` but is *not* a divisor of `z`).

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The `prod_c` support identity: non-anchor root ideals divide `(z)`

`∏_η 𝔞(η) = 𝔷'·𝔭^m` and `(z) = 𝔪·𝔷'`, so for `η ≠ η₀` (where `𝔭 ∤ 𝔞(η)`), `𝔞(η)` divides
`𝔷'·𝔭^m` coprimely to `𝔭`, hence divides `𝔷'`, hence divides `(z)`. -/

set_option maxRecDepth 4000 in
/-- **`∏_η 𝔞(η) = 𝔷'·𝔭^m`** (the `p`-th root of Washington's `prod_c`).  From
`(∏_η 𝔞(η))^p = ∏_η 𝔠(η) = (𝔷'·𝔭^m)^p` (`prod_c` + `root_div_zeta_sub_one_dvd_gcd_spec`), `p`-th
root uniqueness in the ideal monoid gives the unsquared identity. -/
theorem caseII_prod_rootIdeal_eq {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    (∏ η ∈ Finset.attach (nthRootsFinset 37 (1 : 𝓞 K)),
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η) =
      zDivM D.hζ D.equation D.hy *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hpow : (∏ η ∈ Finset.attach (nthRootsFinset 37 (1 : 𝓞 K)),
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η) ^ 37 =
      (zDivM D.hζ D.equation D.hy *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) ^ 37 := by
    rw [← Finset.prod_pow]
    rw [Finset.prod_congr rfl
      (fun η _ ↦ root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η)]
    exact prod_c hp D.hζ D.equation D.hy
  -- `p`-th root uniqueness in the ideal monoid: both `dvd` directions, then `le_antisymm`.
  have hAB := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp hpow.dvd
  have hBA :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp hpow.symm.dvd
  exact le_antisymm (Ideal.dvd_iff_le.mp hBA) (Ideal.dvd_iff_le.mp hAB)

/-- **`zDivM ∣ (z)`** — the `𝔪`-free part `𝔷'` of `(z)` divides `(z)`.  Immediate from
`z_div_m_spec` : `(z) = 𝔪·𝔷'`. -/
theorem caseII_z_div_m_dvd_span_z {m : ℕ} (D : CaseIIData37 K m) :
    zDivM D.hζ D.equation D.hy ∣ Ideal.span ({D.z} : Set (𝓞 K)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact Dvd.intro_left _ (z_div_m_spec D.hζ D.equation D.hy).symm

/-- **Each non-anchor root ideal `𝔞(η)` divides `(z)`** (Washington `Bₐ ∣ (z)`, `a ≥ 1`).

For `η ≠ η₀`, `𝔭 ∤ 𝔞(η)` (`p_dvd_a_iff`), so `𝔞(η)` is coprime to `𝔭`; since `𝔞(η)` divides
`∏_η 𝔞(η) = 𝔷'·𝔭^m` (`caseII_prod_rootIdeal_eq`), coprimality to `𝔭^m` forces `𝔞(η) ∣ 𝔷'`, and
`𝔷' ∣ (z)` (`caseII_z_div_m_dvd_span_z`).  Thus `support(𝔞(η)) ⊆ support(z)`: the nontrivial
adjacent factors `Bₐ`, `a ≥ 1`, are genuine prime factors of the Fermat variable. -/
theorem caseII_rootIdeal_dvd_z {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ zetaSubOneDvdRoot hp D.hζ D.equation D.hy) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ∣ Ideal.span ({D.z} : Set (𝓞 K)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `𝔞(η) ∣ ∏ 𝔞(η) = 𝔷'·𝔭^m`.
  have hdvd_prod : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ∣
      zDivM D.hζ D.equation D.hy *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m := by
    rw [← caseII_prod_rootIdeal_eq D hp]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_attach _ η)
  -- `𝔭 ∤ 𝔞(η)` (η ≠ η₀), so `IsCoprime (𝔭) (𝔞 η)`, hence `IsCoprime (𝔭^m) (𝔞 η)`.
  have hp_not_dvd : ¬ Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η := by
    rw [p_dvd_a_iff hp D.hζ D.equation D.hy]
    exact hη
  have hcop : IsCoprime (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η)
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) := by
    apply IsCoprime.pow_right
    rw [Ideal.isCoprime_iff_gcd, gcd_comm,
      (Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff]
    exact hp_not_dvd
  -- coprime to `𝔭^m`, dividing `𝔷'·𝔭^m`, so `𝔞(η) ∣ 𝔷' ∣ (z)`.
  exact (hcop.dvd_of_dvd_mul_right hdvd_prod).trans (caseII_z_div_m_dvd_span_z D)

/-! ## 2. The strict factor drop from prime-support inclusion

Washington's new variable is `ξ₁ = ρ₀²`, supported only on the anchor `B₀`.  It is **not** a
divisor of the old `z` (it carries `B₀` to the second power), so the divisibility engine
`caseIIZFactorCount_strict_of_dvd_of_extra_prime` does not directly apply.  The faithful engine
compares **prime supports**: the count strictly drops when `support(z') ⊆ support(z)` and some
prime of `(z)` is dropped.  (The `z' ∣ z` hypothesis of the existing engine is one sufficient
route to the support inclusion; this one takes the inclusion directly, matching `ξ₁ = ρ₀²`.) -/

omit [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **Strict factor-count decrease from support inclusion.**  If every prime factor of `(z')` is a
prime factor of `(z)` and some prime `q` divides `(z)` but not `(z')`, the distinct-prime count
strictly decreases.  This is the sound, faithful form of Washington's "`ξ₁ = ρ₀²` has strictly
fewer distinct prime factors than `z`": `support(ξ₁) = support(B₀) ⊊ support(B₀⋯B_{p−1}) =
support(z)`.  Generalises `caseIIZFactorCount_strict_of_dvd_of_extra_prime` (whose `z' ∣ z`
hypothesis is only used to derive this very support inclusion). -/
theorem caseIIZFactorCount_strict_of_support_subset {z' z : 𝓞 K}
    (hsub : (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset ⊆
      (normalizedFactors (Ideal.span ({z} : Set (𝓞 K)))).toFinset)
    {q : Ideal (𝓞 K)}
    (hqz : q ∈ (normalizedFactors (Ideal.span ({z} : Set (𝓞 K)))).toFinset)
    (hqz' : q ∉ (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset) :
    (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset.card <
      (normalizedFactors (Ideal.span ({z} : Set (𝓞 K)))).toFinset.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨q, hqz, hqz'⟩

/-! ## 3. The non-terminal hypothesis yields a nontrivial non-anchor root ideal

The non-terminal hypothesis (the corrected radical `α` at `η = D.etaOne = ζ` is *not* a unit) forces
some non-anchor `𝔞(η) ≠ (1)`.  Contrapositive: if both `𝔞(η) = (1)` and `𝔞(η⁻¹) = (1)` then, by the
proven `caseII_correctedRadical_fractionalIdeal_eq` (`spanSingleton α = (𝔞(η)/𝔞(η⁻¹))^37`),
`spanSingleton α = (1/1)^37 = 1`, so `α` is a unit of `𝓞 K` — the first layer. -/

omit [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **A nonzero element with `spanSingleton α = 1` is the image of a unit.**  If
`spanSingleton (𝓞 K)⁰ α = 1` then both `α` and `α⁻¹` lie in `(1) = algebraMap '' 𝓞 K`, so
`α = algebraMap a`, `α⁻¹ = algebraMap b` with `a·b = 1`, hence `a` is a unit and
`α = algebraMap (unit)`. -/
theorem caseII_isUnit_of_spanSingleton_eq_one {α : K} (hα : α ≠ 0)
    (hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ α = 1) :
    ∃ αU : (𝓞 K)ˣ, α = algebraMap (𝓞 K) K (αU : 𝓞 K) := by
  have hinj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  -- `α ∈ spanSingleton α = 1`, so `α = algebraMap a`.
  have hα_mem : α ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hsp]; exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hα_mem
  -- `α⁻¹ ∈ (spanSingleton α)⁻¹ = 1⁻¹ = 1`, so `α⁻¹ = algebraMap b`.
  have hinv_sp : FractionalIdeal.spanSingleton (𝓞 K)⁰ α⁻¹ = 1 := by
    rw [← FractionalIdeal.spanSingleton_inv, hsp, inv_one]
  have hαinv_mem : α⁻¹ ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hinv_sp]; exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hαinv_mem
  -- `algebraMap (a·b) = α·α⁻¹ = 1`, so `a·b = 1` in `𝓞 K`.
  have hab : a * b = 1 := by
    apply hinj
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hα]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ?_⟩
  rw [← ha]

/-- **The first-layer (terminal) collapse, contrapositive form.**  If the two adjacent root ideals
`𝔞(η)` and `𝔞(η⁻¹)` are both the unit ideal `(1)`, then the corrected radical `α` at `η` is a unit
of `𝓞 K` (`α = algebraMap αU`).  This is the proven first-layer condition `𝔞(η)/𝔞(η⁻¹) = (1)`
implies `α` a unit, via `caseII_correctedRadical_fractionalIdeal_eq`. -/
theorem caseII_correctedRadical_isUnit_of_rootIdeals_eq_one {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (hη : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η = 1)
    (hηinv : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) = 1) :
    ∃ αU : (𝓞 K)ˣ,
      caseII_correctedRadical D η (caseII_correctionUnit η) =
        algebraMap (𝓞 K) K (αU : 𝓞 K) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `spanSingleton α = (𝔞(η)/𝔞(η⁻¹))^37 = (1/1)^37 = 1`.
  have hfrac := caseII_correctedRadical_fractionalIdeal_eq D hp η
  rw [hη, hηinv, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, div_one, one_pow] at hfrac
  -- so `α` is a unit of `𝓞 K`.
  exact caseII_isUnit_of_spanSingleton_eq_one
    (caseII_correctedRadical_ne_zero D hp η (caseII_correctionUnit η)) hfrac

/-- **Non-terminal ⟹ a nontrivial non-anchor root ideal exists.**  If the corrected radical `α` at
`η = D.etaOne = ζ` is **not** a unit of `𝓞 K`, then one of the two non-anchor root ideals
`𝔞(D.etaOne)`, `𝔞(D.etaOne⁻¹)` is `≠ (1)`.  This is the "`Bₐ ≠ (1)` for some `a ≥ 1`" that drives
Washington's strict factor drop, obtained by contraposing
`caseII_correctedRadical_isUnit_of_rootIdeals_eq_one`.  The witnessing root `η₁` satisfies
`η₁ ≠ η₀` (both `D.etaOne` and its inverse are non-anchor). -/
theorem caseII_exists_nontrivial_nonanchor_rootIdeal {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (hnonterm : ¬ ∃ αU : (𝓞 K)ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 K) K (αU : 𝓞 K)) :
    ∃ η₁ : nthRootsFinset 37 (1 : 𝓞 K),
      η₁ ≠ zetaSubOneDvdRoot hp D.hζ D.equation D.hy ∧
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ ≠ 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- the anchor root is `D.etaZero = zetaSubOneDvdRoot ..` (proof-irrelevant `hp`).
  have hηZ : zetaSubOneDvdRoot hp D.hζ D.equation D.hy = D.etaZero := rfl
  have h1_ne : D.etaOne ≠ D.etaZero := D.toCaseIIData37.etaOne_ne_etaZero
  have hinv_ne : caseII_etaInv D.etaOne ≠ D.etaZero := caseII_etaInv_ne_etaZero D hp _ h1_ne
  -- if BOTH root ideals were `(1)`, `α` would be a unit — contradiction.
  by_contra hcon
  push Not at hcon
  have hη1 : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaOne = 1 :=
    hcon D.etaOne (by rw [hηZ]; exact h1_ne)
  have hη1inv :
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaOne) = 1 :=
    hcon (caseII_etaInv D.etaOne) (by rw [hηZ]; exact hinv_ne)
  exact hnonterm (caseII_correctedRadical_isUnit_of_rootIdeals_eq_one D hp D.etaOne hη1 hη1inv)

/-! ## 4. The extra prime of `(z)` not dividing an anchor-supported variable

Combining: a nontrivial non-anchor `𝔞(η₁) ≠ (1)` (from non-terminal) divides `(z)`
(`caseII_rootIdeal_dvd_z`), so any prime factor `q` of `𝔞(η₁)` is a prime factor of `(z)`.  When the
new datum's `z'` is supported only on the anchor `𝔞(η₀)` (`support(z') ⊆ support(𝔞(η₀))`), and the
`𝔞(η)` are pairwise coprime (`coprime_c` via `𝔠`), this `q` is **not** a factor of `(z')` — the
extra prime. -/

/-- **A nontrivial ideal coprime to `𝔭` has a prime factor.**  `𝔞(η₁) ≠ (1)` and `𝔞(η₁) ≠ ⊥` (it
divides the nonzero `(z)`), so it has at least one prime factor `q ∈ normalizedFactors 𝔞(η₁)`. -/
theorem caseII_exists_prime_factor_of_rootIdeal_ne_one {m : ℕ} (D : CaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η₁ : nthRootsFinset 37 (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp D.hζ D.equation D.hy)
    (hne1 : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ ≠ 1) :
    ∃ q ∈ normalizedFactors (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁),
      q ∈ normalizedFactors (Ideal.span ({D.z} : Set (𝓞 K))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `𝔞(η₁) ≠ ⊥`: it divides `(z) ≠ ⊥`.
  have hdvd_z := caseII_rootIdeal_dvd_z D hp η₁ hη₁
  have hz_ne : Ideal.span ({D.z} : Set (𝓞 K)) ≠ 0 := caseIIData37_span_z_ne_bot D
  have ha_ne : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ ≠ 0 := by
    intro h0
    rw [h0] at hdvd_z
    exact hz_ne (zero_dvd_iff.mp hdvd_z)
  -- `𝔞(η₁) ≠ ⊤` (= `(1)`), so it is not a unit, so `normalizedFactors` is nonempty.
  have ha_ne_top : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ ≠ ⊤ := by
    rw [← Ideal.one_eq_top]; exact hne1
  have ha_not_unit : ¬ IsUnit (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁) := by
    rw [Ideal.isUnit_iff]; exact ha_ne_top
  -- a prime factor `q` of `𝔞(η₁)`.
  obtain ⟨q, hq_mem⟩ := exists_mem_normalizedFactors ha_ne ha_not_unit
  refine ⟨q, hq_mem, ?_⟩
  -- `q` irreducible, `q ∣ 𝔞(η₁) ∣ (z)`, so `q ∈ normalizedFactors (z)` (associatedness = equality
  -- for normalized ideal factors).
  have hq_irr : Irreducible q := irreducible_of_normalized_factor q hq_mem
  have hq_dvd_z : q ∣ Ideal.span ({D.z} : Set (𝓞 K)) :=
    (dvd_of_mem_normalizedFactors hq_mem).trans hdvd_z
  obtain ⟨q', hq'_mem, hq'_assoc⟩ := exists_mem_normalizedFactors_of_dvd hz_ne hq_irr hq_dvd_z
  -- `q = q'`: both normalized, `q ~ᵤ q'`.
  have hqq' : q = q' := by
    rw [← normalize_normalized_factor q hq_mem, ← normalize_normalized_factor q' hq'_mem,
      normalize_eq_normalize_iff, dvd_dvd_iff_associated]
    exact hq'_assoc
  rwa [hqq']

/-- **Root ideals are pairwise coprime** (Washington: the `Bₐ` are relatively prime).  From
`coprime_c` (on the `𝔠`-ideals) and `𝔞(η)^37 = 𝔠(η)`: for `η₁ ≠ η₂`, `IsCoprime (𝔞 η₁) (𝔞 η₂)`. -/
theorem caseII_coprime_rootIdeal {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η₁ ≠ η₂) :
    IsCoprime (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁)
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `IsCoprime (𝔞 η₁)^37 (𝔞 η₂)^37` from `coprime_c` via `𝔠 = 𝔞^37`, then strip the powers.
  have hcop_c : IsCoprime (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ ^ 37)
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₂ ^ 37) := by
    rw [root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy,
      root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy]
    exact coprime_c hp D.hζ D.equation D.hy η₁ η₂ hη
  exact (IsCoprime.pow_right_iff (by norm_num)).mp
    ((IsCoprime.pow_left_iff (by norm_num)).mp hcop_c)

/-- **The `𝔭`-free anchor `𝔞₀` divides `(z)`** (Washington's `B₀ ∣ (z)`).  `𝔞₀ ∣ 𝔞(η₀)` and `𝔞₀` is
coprime to `𝔭` (`not_p_div_a_zero`); `𝔞(η₀) ∣ ∏ 𝔞(η) = 𝔷'·𝔭^m` so `𝔞₀ ∣ 𝔷'·𝔭^m`, coprime to `𝔭`,
hence `𝔞₀ ∣ 𝔷' ∣ (z)`. -/
theorem caseII_a_eta_zero_dvd_z {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    aEtaZeroDvdPPow hp D.hζ D.equation D.hy ∣ Ideal.span ({D.z} : Set (𝓞 K)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `𝔞₀ ∣ 𝔞(η₀) ∣ ∏ 𝔞(η) = 𝔷'·𝔭^m`.
  have h𝔞₀_dvd_𝔞 : aEtaZeroDvdPPow hp D.hζ D.equation D.hy ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (zetaSubOneDvdRoot hp D.hζ D.equation D.hy) :=
    Dvd.intro_left _ (a_eta_zero_dvd_p_pow_spec hp D.hζ D.equation D.hy)
  have h𝔞_dvd_prod : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
      (zetaSubOneDvdRoot hp D.hζ D.equation D.hy) ∣
      zDivM D.hζ D.equation D.hy *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m := by
    rw [← caseII_prod_rootIdeal_eq D hp]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_attach _ _)
  have hdvd_prod := h𝔞₀_dvd_𝔞.trans h𝔞_dvd_prod
  -- `𝔭 ∤ 𝔞₀`, so coprime to `𝔭^m`.
  have hcop : IsCoprime (aEtaZeroDvdPPow hp D.hζ D.equation D.hy)
      (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ^ m) := by
    apply IsCoprime.pow_right
    rw [Ideal.isCoprime_iff_gcd, gcd_comm,
      (Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff]
    exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz
  exact (hcop.dvd_of_dvd_mul_right hdvd_prod).trans (caseII_z_div_m_dvd_span_z D)

/-- **The `𝔭`-free anchor `𝔞₀` is coprime to every non-anchor root ideal.**  `𝔞₀ ∣ 𝔞(η₀)` and
`IsCoprime (𝔞 η₀) (𝔞 η₁)` for `η₁ ≠ η₀` (`caseII_coprime_rootIdeal`), so `IsCoprime 𝔞₀ (𝔞 η₁)`.
Hence the prime factors of `𝔞(η₁)` (the dropped `Bₐ`, `a ≥ 1`) are **not** factors of `𝔞₀` (the
anchor `B₀`), the support of the new variable. -/
theorem caseII_coprime_a_eta_zero_rootIdeal {m : ℕ} (D : CaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η₁ : nthRootsFinset 37 (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp D.hζ D.equation D.hy) :
    IsCoprime (aEtaZeroDvdPPow hp D.hζ D.equation D.hy)
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h𝔞₀_dvd_𝔞 : aEtaZeroDvdPPow hp D.hζ D.equation D.hy ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (zetaSubOneDvdRoot hp D.hζ D.equation D.hy) :=
    Dvd.intro_left _ (a_eta_zero_dvd_p_pow_spec hp D.hζ D.equation D.hy)
  exact IsCoprime.of_isCoprime_of_dvd_left
    (caseII_coprime_rootIdeal D hp _ η₁ (fun h ↦ hη₁ h.symm)) h𝔞₀_dvd_𝔞

/-! ## 5. The strict factor drop from an anchor-supported new variable

Assembling the proven pieces: if a new variable `z'` is **anchor-supported**
(`support(z') ⊆ support(𝔞₀)`), then under the non-terminal hypothesis the distinct-prime count
strictly drops.  The dropped prime is any prime factor `q` of a nontrivial non-anchor `𝔞(η₁)`
(`caseII_exists_nontrivial_nonanchor_rootIdeal` + `caseII_exists_prime_factor_of_rootIdeal_ne_one`):
`q ∈ support(z)` (it divides `(z)`), but `q ∉ support(𝔞₀) ⊇ support(z')` because `𝔞₀` is coprime to
`𝔞(η₁)` (`caseII_coprime_a_eta_zero_rootIdeal`).  This is the sound, fully-proven heart of
Washington's "`ξ₁ = ρ₀²` has strictly fewer distinct prime factors than `z`". -/

/-- **The strict factor drop, from an anchor-supported new variable + the non-terminal hypothesis.**

Given a real datum `D` whose adjacent corrected radical at `η = ζ` is **not** a unit (the
non-terminal regime), and a new variable `z'` whose prime support is contained in that of the
`𝔭`-free anchor `𝔞₀ = aEtaZeroDvdPPow` (Washington's `B₀`, `(z') = (ρ₀²) = 𝔞₀²` ⟹
`support(z') = support(𝔞₀)`), the distinct-prime count of `(z')` is **strictly less** than that of
`(D.z)`.

Proof: (i) `support(z') ⊆ support(𝔞₀) ⊆ support(z)` (the anchor `𝔞₀ ∣ (z)`,
`caseII_a_eta_zero_dvd_z`); (ii) the non-terminal hypothesis yields a nontrivial non-anchor
`𝔞(η₁)` with a prime factor `q ∈ support(z)` (`caseII_exists_nontrivial_nonanchor_rootIdeal` +
`caseII_exists_prime_factor_of_rootIdeal_ne_one`); (iii) `q ∉ support(z')` since `q ∣ 𝔞(η₁)`,
`IsCoprime 𝔞₀ 𝔞(η₁)` ⟹ `q ∤ 𝔞₀`, and `support(z') ⊆ support(𝔞₀)`.  Apply
`caseIIZFactorCount_strict_of_support_subset`. -/
theorem caseIIZFactorCount_strict_of_anchor_supported {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (hnonterm : ¬ ∃ αU : (𝓞 K)ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 K) K (αU : 𝓞 K))
    {z' : 𝓞 K}
    (hsupp : (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset ⊆
      (normalizedFactors (aEtaZeroDvdPPow hp D.hζ D.equation D.hy)).toFinset) :
    (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset.card <
      caseIIZFactorCount D.toCaseIIData37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔞₀ := aEtaZeroDvdPPow hp D.hζ D.equation D.hy with h𝔞₀
  have hz_ne : Ideal.span ({D.z} : Set (𝓞 K)) ≠ 0 :=
    caseIIData37_span_z_ne_bot D.toCaseIIData37
  -- `𝔞₀ ∣ (z)`, so `support(𝔞₀) ⊆ support(z)`.
  have h𝔞₀_dvd_z : 𝔞₀ ∣ Ideal.span ({D.z} : Set (𝓞 K)) :=
    caseII_a_eta_zero_dvd_z D.toCaseIIData37 hp
  have h𝔞₀_ne : 𝔞₀ ≠ 0 :=
    fun h0 ↦ hz_ne (by rw [h0] at h𝔞₀_dvd_z; exact zero_dvd_iff.mp h𝔞₀_dvd_z)
  have hsupp_anchor_z : (normalizedFactors 𝔞₀).toFinset ⊆
      (normalizedFactors (Ideal.span ({D.z} : Set (𝓞 K)))).toFinset := by
    intro p hp_mem
    rw [Multiset.mem_toFinset] at hp_mem ⊢
    exact Multiset.subset_of_le
      ((dvd_iff_normalizedFactors_le_normalizedFactors h𝔞₀_ne hz_ne).mp h𝔞₀_dvd_z) hp_mem
  -- chain the support inclusion `support(z') ⊆ support(𝔞₀) ⊆ support(z)`.
  have hsub : (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset ⊆
      (normalizedFactors (Ideal.span ({D.z} : Set (𝓞 K)))).toFinset :=
    hsupp.trans hsupp_anchor_z
  -- the dropped prime: a prime factor `q` of a nontrivial non-anchor `𝔞(η₁)`.
  obtain ⟨η₁, hη₁_ne, hη₁_ne1⟩ := caseII_exists_nontrivial_nonanchor_rootIdeal D hp hnonterm
  obtain ⟨q, hq_a, hq_z⟩ :=
    caseII_exists_prime_factor_of_rootIdeal_ne_one D.toCaseIIData37 hp η₁ hη₁_ne hη₁_ne1
  -- `q ∉ support(𝔞₀)` (coprime to `𝔞(η₁)`), hence `q ∉ support(z')` (⊆ support(𝔞₀)).
  have hq_irr : Irreducible q := irreducible_of_normalized_factor q hq_a
  have hq_dvd_a : q ∣ rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η₁ :=
    dvd_of_mem_normalizedFactors hq_a
  have hq_notMem_anchor : q ∉ (normalizedFactors 𝔞₀).toFinset := by
    intro hq_anchor
    rw [Multiset.mem_toFinset] at hq_anchor
    have hq_dvd_𝔞₀ : q ∣ 𝔞₀ := dvd_of_mem_normalizedFactors hq_anchor
    -- `q ∣ 𝔞₀` and `q ∣ 𝔞(η₁)` with `IsCoprime 𝔞₀ 𝔞(η₁)` ⟹ `q` is a unit, contradiction.
    exact hq_irr.not_isUnit
      ((caseII_coprime_a_eta_zero_rootIdeal D.toCaseIIData37 hp η₁ hη₁_ne).isUnit_of_dvd'
        hq_dvd_𝔞₀ hq_dvd_a)
  have hq_notMem_z' : q ∉ (normalizedFactors (Ideal.span ({z'} : Set (𝓞 K)))).toFinset :=
    fun h ↦ hq_notMem_anchor (hsupp h)
  have hq_z' : q ∈ (normalizedFactors (Ideal.span ({D.z} : Set (𝓞 K)))).toFinset :=
    Multiset.mem_toFinset.mpr hq_z
  exact caseIIZFactorCount_strict_of_support_subset hsub hq_z' hq_notMem_z'

end BernoulliRegular.FLT37.Eichler

end

end

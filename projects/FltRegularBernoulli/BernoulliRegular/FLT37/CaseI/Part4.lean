module

public import BernoulliRegular.FLT37.Hilbert90
public import BernoulliRegular.FLT37.KummerUnits
public import BernoulliRegular.FLT37.Mirimanoff
public import FltRegular.NumberTheory.Cyclotomic.CaseI
public import FltRegular.CaseI.Statement
public import Mathlib.NumberTheory.Bernoulli
public import BernoulliRegular.FLT37.CaseI.Part3


/-!
# FLT case I: composed unit-power decomposition (FLT37e)

Combines two earlier results:

* `fltCaseI_factor_eq_unit_mul_pow_of_regular`: the cyclotomic factor
  `a + ζ^k · b` equals a unit `u_k` times a `p`-th power `γ_k^p` (under
  regularity).
* `exists_zeta_pow_mul_real_eq_unit` (Kummer's lemma): the unit `u_k`
  splits as `ζ^{m_k} · v_k` with `v_k ∈ (𝓞 K⁺)ˣ` real.

Together: under regularity, every cyclotomic factor admits the
decomposition `a + ζ^k b = ζ^{m_k} · algebraMap v_k · γ_k^p`. This is the
shape used by the Mirimanoff-polynomial argument that closes case I.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Local abbreviation for the primitive `p`-th root of unity `ζ` packaged as a
unit of `(𝓞 K)ˣ` (replacing the removed `IsPrimitiveRoot.unit'`). -/
local notation3 "ζcu" =>
  (((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit : (𝓞 K)ˣ)

/-- **Bernoulli divisibility at index `2k = p - n`.** If `n` is in the
range `2 ≤ n ≤ p - 3`, `n` is odd (so `p - n` is even, `p - n = 2k` for
some `k`), and `p ∣ (bernoulli (p - n)).num`, then there exists `k` with
`1 ≤ k`, `2k ≤ p - 3`, `2k = p - n`, and `p ∣ (bernoulli (2k)).num` —
the data of an irregular index of `p`. -/
theorem exists_irregular_index_of_dvd_bernoulli_p_sub
    {p : ℕ} (hp_two : 2 < p) (hp_odd : Odd p) {n : ℕ}
    (hn_two : 2 ≤ n) (hn_le : n ≤ p - 3) (hn_odd : Odd n)
    (h_dvd : (p : ℤ) ∣ (bernoulli (p - n)).num) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ 2 * k = p - n ∧
      (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  -- p - n is even (p odd, n odd).
  rcases hp_odd with ⟨q, hq⟩
  rcases hn_odd with ⟨m, hm⟩
  refine ⟨q - m, ?_, ?_, ?_, ?_⟩
  · -- 1 ≤ q - m: q - m = (p - n) / 2 ≥ 3 / 2 ≥ 1.
    omega
  · -- 2 * (q - m) ≤ p - 3.
    omega
  · -- 2 * (q - m) = p - n.
    omega
  · -- p ∣ B_{2(q-m)} numerator.
    have h_2k_eq : 2 * (q - m) = p - n := by omega
    rw [h_2k_eq]
    exact h_dvd

/-- **Conditional Vandiver III case I contradiction.** Combines the chain:
Mirimanoff polynomial vanishing → Bernoulli divisibility → irregular
index → parity hypothesis violation.

Given the FLT case I solution data with `p ∤ b`, the polynomial-vanishing
predicate, the Mirimanoff–Bernoulli identity predicate, the parity
hypothesis on irregular indices, and a witness `n` with:
* `2 ≤ n ≤ p - 3` (in the Mirimanoff range);
* `n` odd (so `p - n` is even, giving a non-trivial Bernoulli index);
* `n ≡ 3 (mod 4)` (so `(p - n) / 2` is odd, contradicting parity);
* `t ^ n ≠ 1` (so the Mirimanoff identity gives Bernoulli divisibility);

we derive `False`. This is the conditional kernel for `VandiverIIICaseI`,
modulo discharging the polynomial-vanishing predicate and the
Mirimanoff-Bernoulli identity (the remaining substantive content of
`[F37-A]` and `[F37-B]`). -/
private theorem odd_of_p_mod_four_one_n_mod_four_three_aux {p n k : ℕ}
    (h_mod_p : p % 4 = 1) (h_mod_n : n % 4 = 3)
    (h_le : n ≤ p - 3) (h_eq : 2 * k = p - n) :
    Odd k := by
  by_contra h_not_odd
  rw [Nat.not_odd_iff_even] at h_not_odd
  rcases h_not_odd with ⟨j, hj⟩
  have h4j : 4 * j = p - n := by omega
  have h_mod_2 : (p - n) % 4 = 2 := by omega
  omega

/-- **Polynomial vanishing from `MirimanoffBernoulliIdentity` and parity.**

Under the Vandiver III parity hypothesis (every irregular Bernoulli index
of `p` has even `k`) plus `p ≡ 1 (mod 4)`, an odd index `n ∈ [2, p-3]`
with `n ≡ 3 (mod 4)` forces `(p - n)/2` to be odd. Such an irregular
index would violate parity, so `B_{p-n} ≢ 0 (mod p)`. Combined with the
`MirimanoffBernoulliIdentity` product relation
`φ_n(t) · B_{p-n} ≡ 0 (mod p)`, we obtain `φ_n(t) ≡ 0 (mod p)`.

This is the sound replacement of the previously broken
`bernoulli_dvd_of_mirimanoff_polynomial_vanishing` kernel. The classical
Mirimanoff/Vandiver chain runs *via polynomial vanishing*: from `MBI` and
parity, derive `φ_n(t) = 0` for `n ≡ 3 (mod 4)`; specialise to `n = 3`
(the smallest such index) and apply the `φ_3` closed form to obtain
`t = -1`, i.e. `a ≡ b (mod p)`. -/
theorem mirimanoffPolynomial_eval_eq_zero_of_mbi_and_parity
    {p : ℕ} [hp : Fact p.Prime]
    (hp_two : 2 < p) (hp_odd : Odd p)
    (h_mod_4 : p % 4 = 1)
    {a b : ℤ}
    (hMI : MirimanoffBernoulliIdentity p a b)
    (h_parity : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
        (p : ℤ) ∣ (bernoulli (2 * k)).num → Even k)
    {n : ℕ} (hn_odd : Odd n) (hn_two : 2 ≤ n) (hn_le : n ≤ p - 3)
    (hn_mod_4 : n % 4 = 3) :
    (mirimanoffPolynomial p n).aeval
      (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0 := by
  -- Product identity from `MBI` at `n`.
  have h_prod := hMI n hn_odd hn_two hn_le
  -- Parity rules out `B_{p-n} ≡ 0 (mod p)`: it would yield an irregular
  -- index `k = (p-n)/2`, which is odd by the mod-4 calculation.
  have h_B_ne_zero : (((bernoulli (p - n)).num : ℤ) : ZMod p) ≠ 0 := by
    intro h_zero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_zero
    obtain ⟨k, hk_pos, hk_le, hk_eq, hk_dvd⟩ :=
      exists_irregular_index_of_dvd_bernoulli_p_sub hp_two hp_odd hn_two hn_le hn_odd
        (by exact_mod_cast h_zero)
    have hk_even : Even k := h_parity k hk_pos hk_le hk_dvd
    have hk_odd : Odd k :=
      odd_of_p_mod_four_one_n_mod_four_three_aux h_mod_4 hn_mod_4 hn_le hk_eq
    exact (Nat.not_odd_iff_even.mpr hk_even) hk_odd
  -- Product zero with `B ≠ 0` forces `φ_n(t) = 0`.
  rcases mul_eq_zero.mp h_prod with h_phi | h_B
  · exact h_phi
  · exact absurd h_B h_B_ne_zero

/-- **`t = -a · b⁻¹ ≠ 1` from FLT case I.** Under FLT case I (with `p ∤ b`),
the Mirimanoff substitution variable `t = -a · b⁻¹` is not equal to `1` in
`ZMod p`. Reason: `t = 1 ⟹ -a = b ⟹ a + b ≡ 0 (mod p)`, but FLT case I
gives `p ∤ (a + b)` (`fltCaseI_p_not_dvd_a_add_b`). -/
theorem fltCaseI_t_ne_one_of_p_not_dvd
    {p : ℕ} [hp : Fact p.Prime]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hb : ¬ (p : ℤ) ∣ b) :
    (-(a : ZMod p) * ((b : ZMod p))⁻¹) ≠ 1 := by
  intro ht
  have h_b_ne : (b : ZMod p) ≠ 0 := by
    intro hz
    have h_dvd : ((b : ℤ) : ZMod p) = 0 := by exact_mod_cast hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_dvd
    exact hb (by exact_mod_cast h_dvd)
  have h_neg_a_eq_b : -(a : ZMod p) = (b : ZMod p) := by
    have : -(a : ZMod p) * ((b : ZMod p))⁻¹ * (b : ZMod p) =
        1 * (b : ZMod p) := by rw [ht]
    rw [mul_assoc, inv_mul_cancel₀ h_b_ne, mul_one, one_mul] at this
    exact this
  have h_ab_zero : (a + b : ZMod p) = 0 := by
    have : (a : ZMod p) + (b : ZMod p) = 0 := by rw [← h_neg_a_eq_b]; ring
    exact_mod_cast this
  have h_ab_dvd : ((a + b : ℤ) : ZMod p) = 0 := by exact_mod_cast h_ab_zero
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_ab_dvd
  exact (fltCaseI_p_not_dvd_a_add_b heq hc) (by exact_mod_cast h_ab_dvd)

/-- **Coprime-order witness lemma.** For `t` in any monoid with `t ≠ 1`, at
least one of `t ^ 3 ≠ 1` or `t ^ 7 ≠ 1` holds. Used by the two-witness
conditional kernel: if both `t ^ 3 = 1` and `t ^ 7 = 1` then `t ^ 1 = 1`
(since `gcd(3, 7) = 1`, write `1 = 5·3 - 2·7`). -/
theorem exists_coprime_witness_of_ne_one {M : Type*} [Monoid M] {t : M}
    (ht_ne_one : t ≠ 1) :
    t ^ 3 ≠ 1 ∨ t ^ 7 ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨ht3, ht7⟩ := h
  apply ht_ne_one
  have h15 : t ^ 15 = 1 := by rw [show (15 : ℕ) = 3 * 5 from rfl, pow_mul, ht3, one_pow]
  have h14 : t ^ 14 = 1 := by rw [show (14 : ℕ) = 7 * 2 from rfl, pow_mul, ht7, one_pow]
  have : t ^ 15 = t ^ 14 * t := by rw [show (15 : ℕ) = 14 + 1 from rfl, pow_add, pow_one]
  rw [h15, h14, one_mul] at this
  exact this.symm

/-- **Conditional Vandiver III case I from `MirimanoffBernoulliConclusion`.**
Same conclusion as `flt_caseI_contradiction_of_mirimanoff_vandiver` but takes
the higher-level `MirimanoffBernoulliConclusion` predicate directly, sidestepping
the need for the (potentially delicate) `MirimanoffBernoulliIdentity` predicate
to be in its precise classical form. -/
theorem flt_caseI_contradiction_of_bernoulli_conclusion
    {p : ℕ} [_hp : Fact p.Prime]
    (hp_two : 2 < p) (hp_odd : Odd p)
    (h_mod_4 : p % 4 = 1)
    {a b : ℤ}
    (hMC : MirimanoffBernoulliConclusion p a b)
    (h_parity : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
        (p : ℤ) ∣ (bernoulli (2 * k)).num → Even k)
    {n : ℕ} (hn_two : 2 ≤ n) (hn_le : n ≤ p - 3) (hn_odd : Odd n)
    (hn_mod_4 : n % 4 = 3)
    (ht_ne : (-(a : ZMod p) * ((b : ZMod p))⁻¹) ^ n ≠ 1) :
    False := by
  have h_dvd := hMC n hn_two hn_le ht_ne
  obtain ⟨k, hk_pos, hk_le, hk_eq, hk_dvd⟩ :=
    exists_irregular_index_of_dvd_bernoulli_p_sub hp_two hp_odd hn_two hn_le hn_odd h_dvd
  have hk_even : Even k := h_parity k hk_pos hk_le hk_dvd
  have hk_odd : Odd k :=
    odd_of_p_mod_four_one_n_mod_four_three_aux h_mod_4 hn_mod_4 hn_le hk_eq
  exact (Nat.not_odd_iff_even.mpr hk_even) hk_odd

/-- **Strong conditional Vandiver III case I from `MirimanoffBernoulliConclusion`.**
Two-witness version: using `n = 3` and `n = 7` together, removes the
`t^n ≠ 1` hypothesis. -/
theorem flt_caseI_contradiction_of_bernoulli_conclusion_strong
    {p : ℕ} [hp : Fact p.Prime]
    (hp_eleven : 11 ≤ p) (hp_odd : Odd p)
    (h_mod_4 : p % 4 = 1)
    {a b : ℤ}
    (ht_ne_one : (-(a : ZMod p) * ((b : ZMod p))⁻¹) ≠ 1)
    (hMC : MirimanoffBernoulliConclusion p a b)
    (h_parity : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
        (p : ℤ) ∣ (bernoulli (2 * k)).num → Even k) :
    False := by
  have hp_two : 2 < p := by omega
  rcases exists_coprime_witness_of_ne_one ht_ne_one with ht3 | ht7
  · exact flt_caseI_contradiction_of_bernoulli_conclusion
      hp_two hp_odd h_mod_4 hMC h_parity
      (n := 3) (by omega) (by omega) ⟨1, by omega⟩ (by omega) ht3
  · exact flt_caseI_contradiction_of_bernoulli_conclusion
      hp_two hp_odd h_mod_4 hMC h_parity
      (n := 7) (by omega) (by omega) ⟨3, by omega⟩ (by omega) ht7

/-- **Case I + `MirimanoffBernoulliIdentity` + parity gives `a ≡ b (mod p)`.**

This is the main F37-A reduction expressed at the integer level: under
the corrected product-form `MBI` and the Vandiver III parity hypothesis,
any FLT case I solution `(a, b, c)` at `p ≥ 11` with `p ≡ 1 (mod 4)`
satisfies the integer congruence `a ≡ b (mod p)`.

The chain is:
* Apply `mirimanoffPolynomial_eval_eq_zero_of_mbi_and_parity` at `n = 3`
  (`n ≡ 3 (mod 4)`, `2 ≤ n ≤ p - 3`) to obtain `φ_3(t) ≡ 0 (mod p)` for
  `t = -a · b⁻¹`.
* Apply `fltCaseI_phi_3_iff_a_eq_b_mod_p` to convert the polynomial
  vanishing into the integer congruence.

Closing FLT case I from `a ≡ b (mod p)` requires Vandiver Lemma 1
(case II descent, ticket F37-D) and is not in scope here. -/
theorem fltCaseI_a_eq_b_mod_p_of_mbi_and_parity
    {p : ℕ} [hp : Fact p.Prime]
    (hp_eleven : 11 ≤ p) (hp_odd : Odd p) (h_mod_4 : p % 4 = 1)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c)
    (hMI : MirimanoffBernoulliIdentity p a b)
    (h_parity : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
        (p : ℤ) ∣ (bernoulli (2 * k)).num → Even k) :
    (a : ZMod p) = (b : ZMod p) := by
  have hp_two : 2 < p := by omega
  -- Step 1: bridge `MBI` + parity at `n = 3` ⟹ `aeval φ_3 t = 0`.
  have h_phi_3_aeval :
      (mirimanoffPolynomial p 3).aeval
        (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0 :=
    mirimanoffPolynomial_eval_eq_zero_of_mbi_and_parity
      hp_two hp_odd h_mod_4 hMI h_parity
      (n := 3) ⟨1, by omega⟩ (by omega) (by omega) (by omega)
  -- For `ZMod p` over itself, `aeval = eval`.
  have h_phi_3 :
      (mirimanoffPolynomial p 3).eval
        (-(a : ZMod p) * ((b : ZMod p))⁻¹) = 0 := by
    rw [Polynomial.aeval_def] at h_phi_3_aeval
    rwa [show (algebraMap (ZMod p) (ZMod p)) = RingHom.id (ZMod p) from rfl,
        show ((mirimanoffPolynomial p 3).eval₂ (RingHom.id (ZMod p))
              (-(a : ZMod p) * ((b : ZMod p))⁻¹)) =
            (mirimanoffPolynomial p 3).eval
              (-(a : ZMod p) * ((b : ZMod p))⁻¹) from rfl] at h_phi_3_aeval
  -- Step 2: φ_3 vanishing ⟺ `a ≡ b (mod p)` under FLT case I.
  have h_ab : ¬ (p : ℤ) ∣ a + b := fltCaseI_p_not_dvd_a_add_b heq hc
  exact (fltCaseI_phi_3_iff_a_eq_b_mod_p hp_odd ha hb h_ab).mp h_phi_3

/-- **Case I + MBI + parity ⟹ `MirimanoffPolynomialVanishingOdd`.**

Composes `fltCaseI_a_eq_b_mod_p_of_mbi_and_parity` (giving the integer
congruence `a ≡ b (mod p)`) with
`mirimanoffPolynomialVanishingOdd_of_a_eq_b_mod_p` (extending to all odd
`n` via `t = -1` and the standing odd-symmetry fact
`mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd`).

Useful as a packaged statement of the Mirimanoff polynomial-vanishing
side of the F37-A reduction, in the form classically discussed (vanishing
for *all* odd `n` in `[2, p-3]`, not just `n = 3`). -/
theorem mirimanoffPolynomialVanishingOdd_of_mbi_and_parity
    {p : ℕ} [hp : Fact p.Prime]
    (hp_eleven : 11 ≤ p) (hp_odd : Odd p) (h_mod_4 : p % 4 = 1)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c)
    (hMI : MirimanoffBernoulliIdentity p a b)
    (h_parity : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
        (p : ℤ) ∣ (bernoulli (2 * k)).num → Even k) :
    MirimanoffPolynomialVanishingOdd p a b := by
  have h_eq := fltCaseI_a_eq_b_mod_p_of_mbi_and_parity
    hp_eleven hp_odd h_mod_4 heq ha hb hc hMI h_parity
  have h_ab : ¬ (p : ℤ) ∣ a + b := fltCaseI_p_not_dvd_a_add_b heq hc
  exact mirimanoffPolynomialVanishingOdd_of_a_eq_b_mod_p hp_odd ha hb h_ab h_eq

/-! ### Removed: `MV + MBI ⟹ False` chain

The old chain `flt_caseI_contradiction_of_mirimanoff_vandiver(_strong)
(_oddPred)`, `fltCaseI_contradiction_under_predicates(_oddPred)`, and the
specialisations `fltCaseI_contradiction_of_phi_3_vanishing` /
`fltCaseI_contradiction_of_a_eq_b_mod_p` derived `False` from
`MirimanoffPolynomialVanishing(Odd) + MirimanoffBernoulliIdentity +
parity`. The bridge step `MV + MBI ⟹ MirimanoffBernoulliConclusion` was
sound only because the previous (incorrect) `MBI` formulation
`(p-1)·φ_n(t) ≡ -n·B_{p-n}·(1-t^n) (mod p)` algebraically combined with
`φ_n(t) = 0` to yield `B_{p-n} ≡ 0 (mod p)`. With the corrected product
form `φ_n(t) · B_{p-n} ≡ 0 (mod p)`, the same combination becomes
`0 · B_{p-n} = 0`, providing no information about `B_{p-n}` — so the
chain is no longer logically usable.

The mathematically valid chain runs via polynomial vanishing rather than
Bernoulli divisibility (see
`mirimanoffPolynomial_eval_eq_zero_of_mbi_and_parity`): from `MBI` and
parity, derive `φ_n(t) = 0` for `n ≡ 3 (mod 4)`. Specialising to `n = 3`
and using the closed form `φ_3(t)·(t-1)² = t·(t+1)` then yields `t = -1`
(equivalently `a ≡ b (mod p)`). The final closure `a ≡ b ⟹ False` for
the irregular case requires Vandiver Lemma 1 / case II descent (ticket
`F37-D`) and is no longer derivable from `MBI` and parity alone.

Downstream wire-ups in `Final.lean` consequently route through the
`MirimanoffBernoulliConclusion` chain
(`flt_caseI_contradiction_of_bernoulli_conclusion(_strong)`), which
remains sound. -/

/-- **(ζ-1)² coefficient match for the FLT case I cyclotomic factor.**

Under FLT case I + regularity, for `p ≥ 5` and each `k < p`, the case I
decomposition `a + ζ^k b = ζ^m · v · γ^p` (with `v = algebraMap v_plus`
real and `γ ∈ 𝓞 K`) admits an order-3 Taylor coefficient match:

There exist `m : ℕ`, `V₀ M : ℤ`, and `w : 𝓞 K` such that
`(ζ-1)³` divides the difference between `a + ζ^k b` and the explicit
order-3 Taylor expansion `V₀M·(1 + m(ζ-1) + (m.choose 2)(ζ-1)²) + (ζ-1)²·w·M`.

This is the key structural identity for the Mirimanoff polynomial vanishing
argument: comparing coefficients of `(ζ-1)⁰, (ζ-1)¹, (ζ-1)²` gives:
* `(a+b) ≡ V₀·M (mod ζ-1)` — relates `a+b` to a product of integers
* `bk ≡ m·V₀·M (mod ζ-1)` — Mirimanoff relation `bk ≡ m(a+b) (mod p)`
* `b·(k.choose 2) ≡ (m.choose 2)·V₀·M + w (mod ζ-1)` — the (ζ-1)²
  coefficient identity, which is the new constraint at order 2. -/
theorem fltCaseI_taylor_coefficient_match_of_regular
    (hp_five : 5 ≤ p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ (m : ℕ) (V₀ M : ℤ) (w : 𝓞 K),
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣
        (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
          ((V₀ : 𝓞 K) * (M : 𝓞 K) +
            (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) *
              (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) +
            ((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w) *
              (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2)) := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, by omega⟩
  -- Get the case I decomposition.
  obtain ⟨m, v_plus, γ, h_decomp⟩ :=
    fltCaseI_factor_eq_zeta_pow_mul_real_unit_mul_pow_of_regular
      (K := K) (by omega : 2 < p) hp_odd h_reg heq hc hab h_factor_ne_zero hk
  -- h_decomp : a + ζ^k b = ζ^m · algebraMap v_plus · γ^p
  -- Apply order-3 Taylor of v · γ^p (with v = algebraMap v_plus, real).
  have hv_real : ringOfIntegersComplexConj K
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
        (v_plus : 𝓞 (NumberField.maximalRealSubfield K))) =
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
        (v_plus : 𝓞 (NumberField.maximalRealSubfield K)) := by
    rw [IsScalarTower.algebraMap_apply
      (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
      AlgEquiv.commutes]
  obtain ⟨V₀, M, w', hVMw⟩ :=
    exists_int_zetaSubOne_cube_dvd_real_mul_pow_sub (p := p) (K := K)
      hp_five hv_real γ
  -- hVMw : (ζ-1)³ ∣ algebraMap v_plus · γ^p - V₀·M - (ζ-1)²·w'
  -- Apply order-3 Taylor of ζ^m.
  have h_zeta_m :=
    zetaSubOne_cube_dvd_zeta_pow_sub_one_sub_natCast_mul_sub_choose_mul (p := p) (K := K) m
  -- h_zeta_m : (ζ-1)³ ∣ ζ^m - 1 - m(ζ-1) - (m.choose 2)(ζ-1)²
  refine ⟨m, V₀, M, w', ?_⟩
  -- Combine all order-3 expansions.
  -- LHS = a + ζ^k b
  --     = ζ^m · v · γ^p (by h_decomp)
  -- We want LHS - (V₀M + m·V₀M·(ζ-1) + ((m.choose 2)·V₀M + w')·(ζ-1)²) ∈ (ζ-1)³·𝓞 K
  -- Substitute LHS = ζ^m · v · γ^p:
  -- = ζ^m · v · γ^p - V₀M - m·V₀M·(ζ-1) - ((m.choose 2)·V₀M + w')·(ζ-1)²
  -- = ζ^m · (v · γ^p) - V₀M·(1 + m(ζ-1) + (m.choose 2)(ζ-1)²) - w'·(ζ-1)²
  -- Use: ζ^m = 1 + m(ζ-1) + (m.choose 2)(ζ-1)² + (ζ-1)³·a (from h_zeta_m)
  --      v · γ^p = V₀M + (ζ-1)²·w' + (ζ-1)³·b (from hVMw)
  -- ζ^m · v · γ^p =
  --   (1 + m(ζ-1) + (m.choose 2)(ζ-1)² + (ζ-1)³·a)·(V₀M + (ζ-1)²·w' + (ζ-1)³·b)
  -- Mod (ζ-1)³:
  --   ≡ V₀M + m·V₀M·(ζ-1) + ((m.choose 2)·V₀M + w')·(ζ-1)² (mod (ζ-1)³)
  obtain ⟨α, hα⟩ := h_zeta_m
  obtain ⟨β, hβ⟩ := hVMw
  set z : 𝓞 K := (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) with hz_def
  set V := (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
    (v_plus : 𝓞 (NumberField.maximalRealSubfield K)) with hV_def
  -- hα : ζ^m - 1 - m·z - (m.choose 2)·z² = z³·α
  -- hβ : V·γ^p - V₀·M - z²·w' = z³·β
  -- h_decomp : a + ζ^k b = ζ^m · V · γ^p
  -- Want: (a + ζ^k b) - V₀M - m·V₀M·z - ((m.choose 2)·V₀M + w')·z² = z³·?
  -- Rewrite using h_decomp to replace LHS:
  rw [h_decomp]
  -- Now goal involves ζ^m · V · γ^p.
  -- ζ^m = 1 + m·z + (m.choose 2)·z² + z³·α  (from hα)
  -- V·γ^p = V₀·M + z²·w' + z³·β  (from hβ)
  refine ⟨α * (V * γ^p) + ((1 : 𝓞 K) + m * z + (m.choose 2 : 𝓞 K) * z^2) * β +
    w' * ((m : 𝓞 K) + (m.choose 2 : 𝓞 K) * z), ?_⟩
  -- Need: ζ^m · V · γ^p - (RHS) = z³ · (α·V·γ^p + (...)·β)
  have h_zeta_m_eq : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m =
      1 + (m : 𝓞 K) * z + (m.choose 2 : 𝓞 K) * z^2 + z^3 * α := by
    linear_combination hα
  have h_v_gamma_eq : V * γ ^ p = (V₀ : 𝓞 K) * (M : 𝓞 K) + z^2 * w' + z^3 * β := by
    linear_combination hβ
  rw [show
    ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) * V * γ^p =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m * (V * γ^p) by
    rw [Units.val_pow_eq_pow_val,
      show (ζcu : 𝓞 K) = ((zeta_spec p ℚ K).toInteger : 𝓞 K) from IsUnit.unit_spec _]
    ring]
  rw [h_zeta_m_eq, h_v_gamma_eq]
  ring

/-- **Constant term of the (ζ-1)² Taylor match: `p ∣ (a + b) - V₀·M`.**

A clean integer-divisibility consequence of `fltCaseI_taylor_coefficient_match_of_regular`:
reducing the Taylor identity modulo `(ζ-1)` gives `p ∣ (a + b) - V₀·M`. -/
theorem fltCaseI_p_dvd_a_add_b_sub_product_of_regular
    (hp_five : 5 ≤ p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ (V₀ M : ℤ), (p : ℤ) ∣ (a + b - V₀ * M) := by
  obtain ⟨m, V₀, M, w, hw⟩ :=
    fltCaseI_taylor_coefficient_match_of_regular (K := K)
      hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk
  refine ⟨V₀, M, ?_⟩
  -- Strategy: (ζ-1)³ ∣ X with X containing the (a+b) - V₀·M as constant term.
  -- (ζ-1) divides everything in (ζ-1)·𝓞 K. Combined with (ζ-1) ∣ (a + ζ^k b - (a+b)),
  -- we get (ζ-1) ∣ (a+b) - V₀·M, hence p ∣ (a+b) - V₀·M.
  have h_dvd_X : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((V₀ : 𝓞 K) * (M : 𝓞 K) +
          (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) +
          ((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2)) :=
    (dvd_pow_self _ (by norm_num : 3 ≠ 0)).trans hw
  have h_factor_sum : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((a + b : ℤ) : 𝓞 K)) :=
    zetaSubOne_dvd_factor_sub_sum p K a b k
  -- The (ζ-1)¹ and (ζ-1)² coefficient terms in the X are divisible by (ζ-1).
  have h_z : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      ((m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) *
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) :=
    ⟨(m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K), by ring⟩
  have h_z2 : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w) *
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2) := by
    have : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 :=
      dvd_pow_self _ (by norm_num : 2 ≠ 0)
    exact this.mul_left _
  -- Combine: from h_dvd_X (which has all terms), subtract h_factor_sum,
  -- subtract h_z, subtract h_z2, get (ζ-1) ∣ (V₀M - (a+b)) (after sign).
  have h_combined : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((V₀ : 𝓞 K) * (M : 𝓞 K)) - ((a + b : ℤ) : 𝓞 K)) := by
    have h_sub1 := dvd_sub h_factor_sum h_dvd_X
    -- After this, we have (ζ-1) ∣ ((V₀M + extra terms) - (a+b))
    have h_sub2 := dvd_sub h_sub1 h_z
    have h_sub3 := dvd_sub h_sub2 h_z2
    convert h_sub3 using 1
    ring
  have h_cast_dvd : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      ((a + b - V₀ * M : ℤ) : 𝓞 K) := by
    have h_cast : ((a + b - V₀ * M : ℤ) : 𝓞 K) =
        -(((V₀ : 𝓞 K) * (M : 𝓞 K)) - ((a + b : ℤ) : 𝓞 K)) := by
      push_cast; ring
    rw [h_cast]
    exact dvd_neg.mpr h_combined
  exact (zeta_sub_one_dvd_Int_iff (zeta_spec p ℚ K)).mp h_cast_dvd

/-- **Mirimanoff parameter relation in product form via Taylor match.**

A direct corollary of `fltCaseI_taylor_coefficient_match_of_regular` and
`fltCaseI_p_dvd_a_add_b_sub_product_of_regular`: combining the Mirimanoff
witness `m'` (from `fltCaseI_mirimanoff_relation_of_regular`) with the
integer factors `V₀, M` (from the Taylor match) gives:

* `(a + b) ≡ V₀·M (mod p)` (the (ζ-1)⁰ identity)
* `b · k ≡ m' · V₀ · M (mod p)` (combining Mirimanoff with the product form)

This packages the (ζ-1)⁰ and (ζ-1)¹ coefficient identities in joint integer
form, suitable for further deduction. -/
theorem fltCaseI_mirimanoff_taylor_combined_of_regular
    (hp_five : 5 ≤ p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ (m' : ℕ) (V₀ M : ℤ),
      (p : ℤ) ∣ (a + b - V₀ * M) ∧
      (p : ℤ) ∣ (b * k - m' * V₀ * M) := by
  obtain ⟨V₀, M, h_ab⟩ := fltCaseI_p_dvd_a_add_b_sub_product_of_regular (K := K)
    hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk
  obtain ⟨m', hm'⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) (by omega : 2 < p) hp_odd (by omega : 3 ≤ p) h_reg heq hc hab hk
  refine ⟨m', V₀, M, h_ab, ?_⟩
  -- p ∣ (a+b - V₀M), so m' · (a+b - V₀M) ≡ 0 (mod p).
  -- Combined with p ∣ m'·(a+b) - b·k:
  -- p ∣ (m'·(a+b) - b·k) - m'·(a+b - V₀·M) = m'·V₀·M - b·k.
  have h_id : (b * (k : ℤ) - m' * V₀ * M) =
      -((m' * (a + b) - b * (k : ℤ)) - m' * (a + b - V₀ * M)) := by ring
  rw [h_id]
  exact dvd_neg.mpr (dvd_sub hm' (h_ab.mul_left _))

/-- **Cube divisibility for an integer divisible by p (when p ≥ 5).**
For any integer `n` with `p ∣ n` and `p ≥ 5`, `(ζ-1)³ ∣ (n : 𝓞 K)`. -/
private theorem zetaSubOne_cube_dvd_intCast_of_p_dvd
    (hp_five : 5 ≤ p) {n : ℤ} (h : (p : ℤ) ∣ n) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣ ((n : ℤ) : 𝓞 K) := by
  have h_zSubOne_pp : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ (p - 1) ∣ ((p : ℕ) : 𝓞 K) :=
    zetaSubOne_pow_p_sub_one_dvd_p (p := p) (K := K)
  have h_z3_dvd_p : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣ ((p : ℕ) : 𝓞 K) :=
    (pow_dvd_pow _ (by omega : 3 ≤ p - 1)).trans h_zSubOne_pp
  have h_p_cast_eq : ((p : ℕ) : 𝓞 K) = (p : 𝓞 K) := by rfl
  rw [h_p_cast_eq] at h_z3_dvd_p
  rcases h with ⟨q, hq⟩
  have h_n_eq : ((n : ℤ) : 𝓞 K) = (p : 𝓞 K) * ((q : ℤ) : 𝓞 K) := by
    push_cast [hq]; ring
  rw [h_n_eq]
  exact h_z3_dvd_p.mul_right _

/-- **Full (ζ-1)² ZMod p coefficient identity.**

For FLT case I + regularity at index `k` with `p ≥ 5`, there exist
`m : ℕ` and `V₀, M, w_int ∈ ℤ` such that:

* `p ∣ (a + b) - V₀ · M`  ((ζ-1)⁰ identity)
* `p ∣ b · k - m · V₀ · M`  ((ζ-1)¹ identity, Mirimanoff in product form)
* `p ∣ b · (k.choose 2) - (m.choose 2) · V₀ · M - w_int`  ((ζ-1)² identity)

The same `m, V₀, M` simultaneously witness all three identities. The integer
`w_int` is the integer-residue of the (ζ-1)² Taylor coefficient `w` from
`fltCaseI_taylor_coefficient_match_of_regular`. -/
theorem fltCaseI_zmod_taylor_match_of_regular
    (hp_five : 5 ≤ p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ (m : ℕ) (V₀ M w_int : ℤ),
      (p : ℤ) ∣ (a + b - V₀ * M) ∧
      (p : ℤ) ∣ (b * k - m * V₀ * M) ∧
      (p : ℤ) ∣ (b * (k.choose 2 : ℤ) - (m.choose 2 : ℤ) * V₀ * M - w_int) := by
  -- Get m, V₀, M, w from Taylor coefficient match.
  obtain ⟨m, V₀, M, w, hw⟩ :=
    fltCaseI_taylor_coefficient_match_of_regular (K := K)
      hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk
  -- Inline-prove (ζ-1)⁰ identity.
  set z : 𝓞 K := (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) with hz_def
  have h_factor_sum : z ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((a + b : ℤ) : 𝓞 K)) :=
    zetaSubOne_dvd_factor_sub_sum p K a b k
  have h_z_dvd_X : z ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((V₀ : 𝓞 K) * (M : 𝓞 K) + (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) * z +
          ((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w) * z ^ 2)) :=
    (dvd_pow_self _ (by norm_num : 3 ≠ 0)).trans hw
  have h_p_dvd_zero : (p : ℤ) ∣ (a + b - V₀ * M) := by
    have h_z_dvd_diff : z ∣ (((V₀ : 𝓞 K) * (M : 𝓞 K)) - ((a + b : ℤ) : 𝓞 K)) := by
      have h_z_dvd_z : z ∣ ((m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) * z) :=
        ⟨(m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K), by ring⟩
      have h_z_dvd_z2 : z ∣
          (((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w) * z ^ 2) :=
        (dvd_pow_self _ (by norm_num : 2 ≠ 0)).mul_left _
      have h_sub3 := dvd_sub (dvd_sub (dvd_sub h_factor_sum h_z_dvd_X) h_z_dvd_z) h_z_dvd_z2
      convert h_sub3 using 1; ring
    have h_cast_dvd : z ∣ ((a + b - V₀ * M : ℤ) : 𝓞 K) := by
      have h_cast : ((a + b - V₀ * M : ℤ) : 𝓞 K) =
          -(((V₀ : 𝓞 K) * (M : 𝓞 K)) - ((a + b : ℤ) : 𝓞 K)) := by push_cast; ring
      rw [h_cast]; exact dvd_neg.mpr h_z_dvd_diff
    exact (zeta_sub_one_dvd_Int_iff (zeta_spec p ℚ K)).mp h_cast_dvd
  -- Inline-prove (ζ-1)¹ identity using Mirimanoff relation + h_p_dvd_zero.
  have h_p_dvd_one : (p : ℤ) ∣ (b * (k : ℤ) - m * V₀ * M) := by
    obtain ⟨m', hm'⟩ := fltCaseI_mirimanoff_relation_of_regular
      (K := K) (by omega : 2 < p) hp_odd (by omega : 3 ≤ p) h_reg heq hc hab hk
    -- hm' : p ∣ m'·(a+b) - b·k. Note m' might differ from our m.
    -- Approach: extract directly from the Taylor match using (ζ-1)² ∣ X analysis.
    -- We have (ζ-1)² ∣ X and (ζ-1) ∣ ((a+b) - V₀M) [implied by p∣(a+b-V₀M) for p ≥ 3].
    -- Then (ζ-1)² ∣ ... gives (ζ-1)¹ identity. Let me do it this way.
    have h_zsq_dvd_X : z ^ 2 ∣
        (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
          ((V₀ : 𝓞 K) * (M : 𝓞 K) +
            (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) * z +
            ((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w) * z ^ 2)) :=
      (pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans hw
    have h_taylor2 := zetaSubOne_sq_dvd_factor_sub_taylor (p := p) (K := K) a b k
    have h_z2_dvd_z2_term : z ^ 2 ∣
        (((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w) * z ^ 2) :=
      ⟨((m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) + w), by ring⟩
    -- (ζ-1)² ∣ ((a+b) + bk(ζ-1)) - (V₀M + mV₀M(ζ-1))
    -- This comes from (h_zsq_dvd_X - h_taylor2) + h_z2_dvd_z2_term, since
    -- the (ζ-1)² terms cancel.
    have h_zsq_dvd_step : z ^ 2 ∣
        (((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K) * (k : 𝓞 K) * z -
          ((V₀ : 𝓞 K) * (M : 𝓞 K) +
            (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) * z)) := by
      have h_diff := dvd_sub h_zsq_dvd_X h_taylor2
      have h_combined := dvd_add h_diff h_z2_dvd_z2_term
      convert h_combined using 1
      ring
    -- Now use h_p_dvd_zero to conclude p ∣ b·k - m·V₀·M
    have h_z2_dvd_const : z ^ 2 ∣ ((a + b - V₀ * M : ℤ) : 𝓞 K) := by
      have h_z3_dvd : z ^ 3 ∣ ((a + b - V₀ * M : ℤ) : 𝓞 K) :=
        zetaSubOne_cube_dvd_intCast_of_p_dvd hp_five h_p_dvd_zero
      exact (pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans h_z3_dvd
    -- (ζ-1)² ∣ h_zsq_dvd_step's expression, and (ζ-1)² ∣ (a+b - V₀M).
    -- Subtract: (ζ-1)² ∣ ((bk - mV₀M)·(ζ-1)).
    have h_z2_dvd_z_term : z ^ 2 ∣
        ((b : 𝓞 K) * (k : 𝓞 K) * z - ((m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) * z)) := by
      have h_z2_dvd_const' : z ^ 2 ∣ (((a + b : ℤ) : 𝓞 K) - ((V₀ * M : ℤ) : 𝓞 K)) := by
        have h_eq2 : (((a + b : ℤ) : 𝓞 K) - ((V₀ * M : ℤ) : 𝓞 K)) =
            ((a + b - V₀ * M : ℤ) : 𝓞 K) := by push_cast; ring
        rw [h_eq2]; exact h_z2_dvd_const
      have h_sub := dvd_sub h_zsq_dvd_step h_z2_dvd_const'
      convert h_sub using 1
      push_cast; ring
    -- (ζ-1)² ∣ X·(ζ-1) ⟹ (ζ-1) ∣ X (where X = (b·k - m·V₀·M : 𝓞 K)).
    have h_z_dvd_diff : z ∣ ((b * (k : ℤ) - m * V₀ * M : ℤ) : 𝓞 K) := by
      have h_eq : (b : 𝓞 K) * (k : 𝓞 K) * z -
            ((m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) * z) =
          ((b * (k : ℤ) - m * V₀ * M : ℤ) : 𝓞 K) * z := by push_cast; ring
      rw [h_eq] at h_z2_dvd_z_term
      rcases h_z2_dvd_z_term with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      have hz_ne : z ≠ 0 := zetaSubOne_ne_zero p K
      have h_factor_eq : ((b * (k : ℤ) - m * V₀ * M : ℤ) : 𝓞 K) * z =
          (z * r) * z := by rw [hr]; ring
      exact mul_right_cancel₀ hz_ne h_factor_eq
    exact (zeta_sub_one_dvd_Int_iff (zeta_spec p ℚ K)).mp h_z_dvd_diff
  -- Get w_int with (ζ-1) ∣ w - w_int.
  obtain ⟨w_int, w', hw_int⟩ : ∃ w_int : ℤ, ∃ w' : 𝓞 K,
      w - (w_int : 𝓞 K) = z * w' := by
    obtain ⟨w_int, hw_int_dvd⟩ := exists_int_zetaSubOne_dvd_sub (p := p) (K := K) w
    obtain ⟨w', hw'⟩ := hw_int_dvd
    exact ⟨w_int, w', hw'⟩
  refine ⟨m, V₀, M, w_int, h_p_dvd_zero, h_p_dvd_one, ?_⟩
  -- (ζ-1)² ZMod p identity.
  -- We have (ζ-1)³ ∣ X and (ζ-1)³ ∣ (a+b - V₀M) and (ζ-1)³ ∣ (b·k - m·V₀M)·(ζ-1)
  -- (the latter from p ∣ b·k - m·V₀M and (ζ-1)^p ∣ p·(ζ-1) ⊆ (ζ-1)³ for p ≥ 4).
  -- Combined: (ζ-1)³ ∣ ((m.choose 2)·V₀·M + w - b·(k.choose 2))·(ζ-1)²
  -- ⟹ (ζ-1) ∣ ((m.choose 2)·V₀·M + w - b·(k.choose 2))
  -- ⟹ (ζ-1) ∣ ((m.choose 2)·V₀·M + w_int - b·(k.choose 2))  [using hw_int]
  -- ⟹ p ∣ ((m.choose 2)·V₀·M + w_int - b·(k.choose 2)) (integer)
  -- ⟹ p ∣ (b·(k.choose 2) - (m.choose 2)·V₀·M - w_int).
  have h_z3_dvd_zero : z ^ 3 ∣ ((a + b - V₀ * M : ℤ) : 𝓞 K) :=
    zetaSubOne_cube_dvd_intCast_of_p_dvd hp_five h_p_dvd_zero
  have h_z3_dvd_one : z ^ 3 ∣ ((b * (k : ℤ) - m * V₀ * M : ℤ) : 𝓞 K) :=
    zetaSubOne_cube_dvd_intCast_of_p_dvd hp_five h_p_dvd_one
  have h_z3_dvd_one_z : z ^ 3 ∣
      (((b * (k : ℤ) - m * V₀ * M : ℤ) : 𝓞 K) * z) :=
    h_z3_dvd_one.mul_right z
  -- Order-3 Taylor of factor.
  have h_taylor3 := zetaSubOne_cube_dvd_factor_sub_taylor2 (p := p) (K := K) a b k
  -- X - Y where X = factor - (V₀M + mV₀Mz + ((m.choose 2)V₀M + w)z²)
  --        Y = factor - ((a+b) + bkz + b(k.choose 2)z²)
  -- X - Y = ((a+b) - V₀M) + (bk - mV₀M)z + (b(k.choose 2) - (m.choose 2)V₀M - w)z²
  have h_z3_dvd_combined : z ^ 3 ∣
      (((a + b : ℤ) : 𝓞 K) - (V₀ : 𝓞 K) * (M : 𝓞 K) +
        ((b : 𝓞 K) * (k : 𝓞 K) - (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K)) * z +
        ((b : 𝓞 K) * (k.choose 2 : 𝓞 K) -
          (m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) - w) * z ^ 2) := by
    have h_diff := dvd_sub hw h_taylor3
    convert h_diff using 1
    push_cast; ring
  -- Cast h_z3_dvd_zero to the matching form.
  have h_const_dvd : z ^ 3 ∣ (((a + b : ℤ) : 𝓞 K) - (V₀ : 𝓞 K) * (M : 𝓞 K)) := by
    have h_eq : ((a + b : ℤ) : 𝓞 K) - (V₀ : 𝓞 K) * (M : 𝓞 K) =
        ((a + b - V₀ * M : ℤ) : 𝓞 K) := by push_cast; ring
    rw [h_eq]; exact h_z3_dvd_zero
  -- Cast h_z3_dvd_one_z to the matching form.
  have h_z_dvd_diff : z ^ 3 ∣
      ((b : 𝓞 K) * (k : 𝓞 K) - (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K)) * z := by
    have h_eq : ((b : 𝓞 K) * (k : 𝓞 K) - (m : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K)) * z =
        ((b * (k : ℤ) - m * V₀ * M : ℤ) : 𝓞 K) * z := by push_cast; ring
    rw [h_eq]; exact h_z3_dvd_one_z
  -- Subtract: z³ ∣ (b(k.choose 2) - (m.choose 2)V₀M - w)·z².
  have h_z3_dvd_z2_term : z ^ 3 ∣
      ((b : 𝓞 K) * (k.choose 2 : 𝓞 K) -
        (m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) - w) * z ^ 2 := by
    have h_sub := dvd_sub (dvd_sub h_z3_dvd_combined h_const_dvd) h_z_dvd_diff
    convert h_sub using 1; ring
  -- Cancel z² in h_z3_dvd_z2_term to get z ∣ (b(k.choose 2) - (m.choose 2)V₀M - w).
  have h_z_dvd_z2_factor : z ∣
      ((b : 𝓞 K) * (k.choose 2 : 𝓞 K) -
        (m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) - w) := by
    rcases h_z3_dvd_z2_term with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have hz_ne : z ≠ 0 := zetaSubOne_ne_zero p K
    have hz2_ne : z ^ 2 ≠ 0 := pow_ne_zero _ hz_ne
    have h_factor_eq : ((b : 𝓞 K) * (k.choose 2 : 𝓞 K) -
          (m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) - w) * z ^ 2 =
        (z * r) * z ^ 2 := by
      have h_z3_eq : z ^ 3 = z * z ^ 2 := by ring
      rw [h_z3_eq] at hr
      linear_combination hr
    exact mul_right_cancel₀ hz2_ne h_factor_eq
  -- Now combine with hw_int: w - w_int = z·w'.
  -- (ζ-1) ∣ b(k.choose 2) - (m.choose 2)V₀M - w
  -- = b(k.choose 2) - (m.choose 2)V₀M - w_int - z·w'
  -- ≡ b(k.choose 2) - (m.choose 2)V₀M - w_int (mod z)
  have h_z_dvd_int : z ∣
      ((b * (k.choose 2 : ℤ) - (m.choose 2 : ℤ) * V₀ * M - w_int : ℤ) : 𝓞 K) := by
    have h_eq : ((b * (k.choose 2 : ℤ) - (m.choose 2 : ℤ) * V₀ * M - w_int : ℤ) : 𝓞 K) =
        ((b : 𝓞 K) * (k.choose 2 : 𝓞 K) -
          (m.choose 2 : 𝓞 K) * (V₀ : 𝓞 K) * (M : 𝓞 K) - w) +
        (w - (w_int : 𝓞 K)) := by push_cast; ring
    rw [h_eq]
    refine dvd_add h_z_dvd_z2_factor ?_
    exact ⟨w', hw_int⟩
  exact (zeta_sub_one_dvd_Int_iff (zeta_spec p ℚ K)).mp h_z_dvd_int

/-- **Simplified (ζ-1)² ZMod p coefficient identity.**

This is a corollary of `fltCaseI_zmod_taylor_match_of_regular` that
substitutes `V₀ · M ≡ a + b (mod p)` (from the (ζ-1)⁰ identity) into the
(ζ-1)¹ and (ζ-1)² identities. After this substitution we obtain:

* `p ∣ b · k - m · (a + b)`  (Mirimanoff relation in standard form)
* `p ∣ b · (k.choose 2) - (m.choose 2) · (a + b) - w_int`

This is the form most useful for the Galois descent step toward
Mirimanoff polynomial vanishing — `(a + b)` is a fixed quantity
independent of `k`, while `m` and `w_int` carry the per-`k` information. -/
theorem fltCaseI_zmod_taylor_simplified_of_regular
    (hp_five : 5 ≤ p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ (m : ℕ) (w_int : ℤ),
      (p : ℤ) ∣ (b * k - m * (a + b)) ∧
      (p : ℤ) ∣ (b * (k.choose 2 : ℤ) - (m.choose 2 : ℤ) * (a + b) - w_int) := by
  obtain ⟨m, V₀, M, w_int, h_zero, h_one, h_two⟩ :=
    fltCaseI_zmod_taylor_match_of_regular (K := K)
      hp_five hp_odd h_reg heq hc hab h_factor_ne_zero hk
  refine ⟨m, w_int, ?_, ?_⟩
  · -- p ∣ b·k - m·(a+b).
    -- We have p ∣ b·k - m·V₀·M and p ∣ a+b - V₀·M.
    -- Multiply the second by m: p ∣ m·(a+b) - m·V₀·M.
    -- Subtract: p ∣ (b·k - m·V₀·M) - (m·(a+b) - m·V₀·M) = b·k - m·(a+b).
    have h_m_dvd : (p : ℤ) ∣ ((m : ℤ) * (a + b) - (m : ℤ) * V₀ * M) := by
      have h_eq : (m : ℤ) * (a + b) - (m : ℤ) * V₀ * M =
          (m : ℤ) * (a + b - V₀ * M) := by ring
      rw [h_eq]; exact h_zero.mul_left _
    have h_sub := h_one.sub h_m_dvd
    have h_eq : b * (k : ℤ) - (m : ℤ) * V₀ * M -
        ((m : ℤ) * (a + b) - (m : ℤ) * V₀ * M) =
        b * (k : ℤ) - (m : ℤ) * (a + b) := by ring
    rwa [h_eq] at h_sub
  · -- p ∣ b·(k.choose 2) - (m.choose 2)·(a+b) - w_int.
    -- Similarly use p ∣ a+b - V₀·M weighted by (m.choose 2).
    have h_mc_dvd : (p : ℤ) ∣
        ((m.choose 2 : ℤ) * (a + b) - (m.choose 2 : ℤ) * V₀ * M) := by
      have h_eq : (m.choose 2 : ℤ) * (a + b) - (m.choose 2 : ℤ) * V₀ * M =
          (m.choose 2 : ℤ) * (a + b - V₀ * M) := by ring
      rw [h_eq]; exact h_zero.mul_left _
    have h_sub := h_two.sub h_mc_dvd
    have h_eq : b * (k.choose 2 : ℤ) - (m.choose 2 : ℤ) * V₀ * M - w_int -
        ((m.choose 2 : ℤ) * (a + b) - (m.choose 2 : ℤ) * V₀ * M) =
        b * (k.choose 2 : ℤ) - (m.choose 2 : ℤ) * (a + b) - w_int := by ring
    rwa [h_eq] at h_sub

end FLT37

end BernoulliRegular

end

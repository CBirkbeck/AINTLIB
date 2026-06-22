module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.FLT37.Principalization
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import BernoulliRegular.FLT37.Mirimanoff.Part2

/-!
# Mirimanoff subfield trick (ticket FLT37d, scaffold)

For an odd prime `ℓ ≡ 1 (mod 4)`, the "Mirimanoff trick" uses the fact
that `-1` is a square mod `ℓ` (so `(ZMod ℓ)ˣ` has an element of order 4).
The corresponding Galois automorphism `ζ ↦ ζ^ω` (where `ω² = -1` in
`ZMod ℓ`) generates a cyclic subgroup of order 4 in `Gal(K/ℚ)`.

The fixed field `k' ⊂ K⁺` of the order-2 subgroup gives a subfield
where Vandiver's odd-index analysis simplifies.

This file establishes the basic infrastructure: the Mirimanoff square
root `ω` and its key properties.

## References

* Vandiver 1929, *FLT and the Second Factor in the Cyclotomic Class Number*.
* Borevich–Shafarevich, *Number Theory*, §4.9.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

section MirimanoffPolynomial

/-- For odd `n`, `φ_n(-1) = 0` in `ZMod p`, expressed via `IsRoot`. -/
theorem mirimanoffPolynomial_neg_one_isRoot_of_odd (p : ℕ) [Fact p.Prime]
    (hp_odd : Odd p) {n : ℕ} (hn : 1 ≤ n) (hn_odd : Odd n) :
    (mirimanoffPolynomial p n).IsRoot (-1) :=
  mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd p hp_odd hn hn_odd

/-- For odd `n` (and odd `p`), `X + 1` divides `mirimanoffPolynomial p n`
in `(ZMod p)[X]`. -/
theorem X_add_one_dvd_mirimanoffPolynomial_of_odd (p : ℕ) [Fact p.Prime]
    (hp_odd : Odd p) {n : ℕ} (hn : 1 ≤ n) (hn_odd : Odd n) :
    (Polynomial.X + 1 : Polynomial (ZMod p)) ∣ mirimanoffPolynomial p n := by
  have h_root := mirimanoffPolynomial_neg_one_isRoot_of_odd p hp_odd hn hn_odd
  have : Polynomial.X - Polynomial.C (-1) = (Polynomial.X + 1 : Polynomial (ZMod p)) := by
    rw [Polynomial.C_neg, Polynomial.C_1, sub_neg_eq_add]
  rw [← this]
  exact Polynomial.dvd_iff_isRoot.mpr h_root

/-- For odd `n` (and odd `p`), `X · (X + 1)` divides `mirimanoffPolynomial p n`. -/
theorem X_mul_X_add_one_dvd_mirimanoffPolynomial_of_odd (p : ℕ) [Fact p.Prime]
    (hp_odd : Odd p) {n : ℕ} (hn : 1 ≤ n) (hn_odd : Odd n) :
    (Polynomial.X * (Polynomial.X + 1) : Polynomial (ZMod p)) ∣
      mirimanoffPolynomial p n := by
  have hcop : IsCoprime (Polynomial.X : Polynomial (ZMod p)) (Polynomial.X + 1) :=
    ⟨-1, 1, by ring⟩
  exact hcop.mul_dvd (X_dvd_mirimanoffPolynomial p n)
    (X_add_one_dvd_mirimanoffPolynomial_of_odd p hp_odd hn hn_odd)

/-- For `2 ≤ n ≤ p - 1`, `X - 1` divides `mirimanoffPolynomial p n`
in `(ZMod p)[X]`. (`φ_n(1) = 0` in this range.) -/
theorem X_sub_one_dvd_mirimanoffPolynomial_of_le (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn_ge : 2 ≤ n) (hn_le : n ≤ p - 1) :
    (Polynomial.X - 1 : Polynomial (ZMod p)) ∣ mirimanoffPolynomial p n := by
  have h_root : (mirimanoffPolynomial p n).IsRoot 1 :=
    mirimanoffPolynomial_eval_one_eq_zero p hn_ge hn_le
  have hC1 : (Polynomial.X - Polynomial.C (1 : ZMod p) : Polynomial (ZMod p)) =
      Polynomial.X - 1 := by simp
  rw [← hC1]
  exact Polynomial.dvd_iff_isRoot.mpr h_root

/-- For `2 ≤ n ≤ p - 1`, `X · (X - 1)` divides `mirimanoffPolynomial p n`. -/
theorem X_mul_X_sub_one_dvd_mirimanoffPolynomial_of_le (p : ℕ) [Fact p.Prime]
    {n : ℕ} (hn_ge : 2 ≤ n) (hn_le : n ≤ p - 1) :
    (Polynomial.X * (Polynomial.X - 1) : Polynomial (ZMod p)) ∣
      mirimanoffPolynomial p n := by
  have hcop : IsCoprime (Polynomial.X : Polynomial (ZMod p)) (Polynomial.X - 1) :=
    ⟨1, -1, by ring⟩
  exact hcop.mul_dvd (X_dvd_mirimanoffPolynomial p n)
    (X_sub_one_dvd_mirimanoffPolynomial_of_le p hn_ge hn_le)

/-- For odd `n` with `2 ≤ n ≤ p - 1` (and odd `p`), the polynomial
`X · (X - 1) · (X + 1)` divides `mirimanoffPolynomial p n`. This combines
the three root conditions `φ_n(0) = 0`, `φ_n(1) = 0`, and `φ_n(-1) = 0`. -/
theorem X_mul_X_sub_one_mul_X_add_one_dvd_mirimanoffPolynomial
    (p : ℕ) [hp : Fact p.Prime] (hp_odd : Odd p) {n : ℕ}
    (hn_ge : 2 ≤ n) (hn_le : n ≤ p - 1) (hn_odd : Odd n) :
    (Polynomial.X * (Polynomial.X - 1) * (Polynomial.X + 1) :
        Polynomial (ZMod p)) ∣ mirimanoffPolynomial p n := by
  -- 2 is a unit in ZMod p for odd p.
  have hp_three : 3 ≤ p := by
    rcases hp_odd with ⟨k, hk⟩
    have := hp.1.two_le
    omega
  have h_two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hp_dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd
    omega
  obtain ⟨v, hv⟩ : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr h_two_ne
  -- Coprimality of `X` and `X + 1`.
  have hX_X_add : IsCoprime (Polynomial.X : Polynomial (ZMod p)) (Polynomial.X + 1) :=
    ⟨-1, 1, by ring⟩
  -- Coprimality of `X - 1` and `X + 1` via Bezout: (-1/2)(X-1) + (1/2)(X+1) = 1.
  have hXm1_X_add : IsCoprime ((Polynomial.X - 1 : Polynomial (ZMod p)))
      (Polynomial.X + 1) := by
    refine ⟨- (Polynomial.C ((v : ZMod p)⁻¹)), Polynomial.C ((v : ZMod p)⁻¹), ?_⟩
    have h_inv : ((v : ZMod p)⁻¹ : ZMod p) * 2 = 1 := by
      rw [← hv]
      exact inv_mul_cancel₀ (Units.ne_zero v)
    have h_C_two : (Polynomial.C (2 : ZMod p) : Polynomial (ZMod p)) =
        (2 : Polynomial (ZMod p)) := by
      rw [show (2 : ZMod p) = (1 : ZMod p) + 1 from by norm_num,
        show (2 : Polynomial (ZMod p)) = 1 + 1 from by norm_num]
      simp [Polynomial.C_add]
    calc (-(Polynomial.C ((v : ZMod p)⁻¹)) * (Polynomial.X - 1) +
            Polynomial.C ((v : ZMod p)⁻¹) * (Polynomial.X + 1) :
          Polynomial (ZMod p))
        = Polynomial.C ((v : ZMod p)⁻¹) * 2 := by ring
      _ = Polynomial.C ((v : ZMod p)⁻¹) * Polynomial.C 2 := by rw [← h_C_two]
      _ = Polynomial.C ((v : ZMod p)⁻¹ * 2) := by rw [Polynomial.C_mul]
      _ = Polynomial.C 1 := by rw [h_inv]
      _ = 1 := Polynomial.C_1
  have hcop : IsCoprime
      ((Polynomial.X * (Polynomial.X - 1) : Polynomial (ZMod p)))
      (Polynomial.X + 1) :=
    hX_X_add.mul_left hXm1_X_add
  exact hcop.mul_dvd
    (X_mul_X_sub_one_dvd_mirimanoffPolynomial_of_le p hn_ge hn_le)
    (X_add_one_dvd_mirimanoffPolynomial_of_odd p hp_odd (by omega) hn_odd)

/-- Stronger consequence: for odd `n` (and odd `p`), the constant term
of `φ_n / (X · (X + 1))` is `0` only at `X = 0`. Equivalently, the
quotient polynomial's eval at `t` for `t ≠ 0, -1` may be non-zero. -/
theorem mirimanoffPolynomial_eval_neg_one_of_odd_eq_zero
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p) {n : ℕ} (hn : 1 ≤ n) (hn_odd : Odd n) :
    (mirimanoffPolynomial p n).eval (-1 : ZMod p) = 0 :=
  mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd p hp_odd hn hn_odd

/-- For every `t ∈ ZMod p \ {1}`, `t` is a root of `φ_p` (as a Finset
membership statement). -/
theorem mirimanoffPolynomial_at_p_isRoot_of_mem_erase (p : ℕ) [Fact p.Prime]
    {t : ZMod p} (ht : t ∈ (Finset.univ.erase (1 : ZMod p))) :
    (mirimanoffPolynomial p p).IsRoot t :=
  mirimanoffPolynomial_at_p_isRoot p (Finset.mem_erase.mp ht).1

/-- For any unit `t : (ZMod p)ˣ` with `(t : ZMod p) ≠ 1`, evaluating `φ_p`
at `(t : ZMod p)` gives `0`. -/
theorem mirimanoffPolynomial_at_p_eval_units_eq_zero (p : ℕ) [Fact p.Prime]
    (t : (ZMod p)ˣ) (ht : (t : ZMod p) ≠ 1) :
    (mirimanoffPolynomial p p).eval (t : ZMod p) = 0 :=
  mirimanoffPolynomial_at_p_eval_eq_zero_of_ne_one p _ ht

/-- **Cyclotomic `x^p + y^p` factorization.** For odd prime `p` and
`x, y ∈ K = ℚ(ζ_p)`, `x^p + y^p = ∏_{ζ p-th root of 1} (x + ζ · y)`.
This is the foundational identity for the Case I Mirimanoff argument. -/
theorem pow_add_pow_eq_prod_zeta_mul (p : ℕ) [hp : Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (x y : K) :
    x ^ p + y ^ p = ∏ ζ ∈ Polynomial.nthRootsFinset p (1 : K), (x + ζ * y) :=
  IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul (x := x) (y := y) hp_odd
    (IsCyclotomicExtension.zeta_spec p ℚ K)

/-- **Cyclotomic `x^p - y^p` factorization** (dual form). For prime `p` and
`x, y ∈ K = ℚ(ζ_p)`,
`x^p - y^p = ∏_{ζ p-th root of 1} (x - ζ · y)`. -/
theorem pow_sub_pow_eq_prod_zeta_mul (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (x y : K) :
    x ^ p - y ^ p = ∏ ζ ∈ Polynomial.nthRootsFinset p (1 : K), (x - ζ * y) :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).pow_sub_pow_eq_prod_sub_mul x y hp.1.pos

/-- The cardinality of `nthRootsFinset p (1 : K)` for `K = ℚ(ζ_p)` is `p`. -/
theorem card_nthRootsFinset_eq_card (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    (Polynomial.nthRootsFinset p (1 : K)).card = p :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).card_nthRootsFinset

/-- The set of `p`-th roots of unity in `K = ℚ(ζ_p)` is the image of
`Finset.range p` under `k ↦ ζ^k`. -/
theorem nthRootsFinset_eq_image_range (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    haveI : DecidableEq K := Classical.decEq K
    Polynomial.nthRootsFinset p (1 : K) =
      (Finset.range p).image
        (fun k => (IsCyclotomicExtension.zeta p ℚ K) ^ k) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro ζ hζ
    rw [Finset.mem_image]
    have hζ' : ζ ^ p = 1 := (Polynomial.mem_nthRootsFinset hp.1.pos 1).mp hζ
    obtain ⟨k, hk_lt, hk_eq⟩ :=
      (IsCyclotomicExtension.zeta_spec p ℚ K).eq_pow_of_pow_eq_one hζ'
    exact ⟨k, Finset.mem_range.mpr hk_lt, hk_eq⟩
  · rw [card_nthRootsFinset_eq_card]
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_range]

/-- Distinct `p`-th roots of unity in `K = ℚ(ζ_p)` differ by an
associate of `ζ - 1`. -/
theorem nthRootsFinset_pairwise_associated_sub (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Set.Pairwise (Polynomial.nthRootsFinset p (1 : K))
      (fun η₁ η₂ => Associated (IsCyclotomicExtension.zeta p ℚ K - 1) (η₁ - η₂)) :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
    hp.1

/-- 𝓞 K-level: distinct integer-form p-th roots of unity differ by an
associate of `ζ.toInteger - 1` (which is the `zetaSubOne` element). -/
theorem nthRootsFinset_pairwise_associated_sub_intForm (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Set.Pairwise (Polynomial.nthRootsFinset p (1 : 𝓞 K))
      (fun η₁ η₂ => Associated
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1) (η₁ - η₂)) :=
  IsPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot hp.1

/-- For two FLT factors `(a + η₁ b)` and `(a + η₂ b)` with η₁ ≠ η₂ p-th
roots of unity, their difference is `(η₁ - η₂) · b`. Foundational for
case I coprimality. -/
theorem fltCaseI_factor_sub (K : Type*) [CommRing K] (a b : K) (η₁ η₂ : K) :
    (a + η₁ * b) - (a + η₂ * b) = (η₁ - η₂) * b := by ring

/-- If a prime `𝔮 : 𝓞 K` divides both `(a + ζ^k · b)` and `b`, then
`𝔮 ∣ a`. -/
theorem dvd_intCast_of_dvd_factor_and_intCast (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {𝔮 : 𝓞 K} (a b : ℤ) (k : ℕ)
    (h_factor : 𝔮 ∣ ((a : 𝓞 K) +
      (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)))
    (hb : 𝔮 ∣ ((b : 𝓞 K))) : 𝔮 ∣ ((a : 𝓞 K)) := by
  have h_mul : 𝔮 ∣ (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k *
      (b : 𝓞 K) := hb.mul_left _
  have := dvd_sub h_factor h_mul
  simpa using this

/-- For two distinct factors `(a + ζ^k b)` and `(a + ζ^l b)` (k ≠ l in
`[0, p)`), their difference equals `(ζ^k - ζ^l) · b` in `𝓞 K`. -/
theorem fltCaseI_factor_sub_intForm (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a b : ℤ) (k l : ℕ) :
    (((a : 𝓞 K) + (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k *
      (b : 𝓞 K)) -
     ((a : 𝓞 K) + (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l *
      (b : 𝓞 K))) =
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k -
       (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l) * (b : 𝓞 K) := by
  ring

/-- For any natural `k`, `ζ^k ∈ nthRootsFinset p (1 : 𝓞 K)` (the integer-form). -/
theorem zeta_pow_mem_nthRootsFinset (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] (k : ℕ) :
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k ∈
      Polynomial.nthRootsFinset p (1 : 𝓞 K) := by
  rw [Polynomial.mem_nthRootsFinset hp.1.pos, ← pow_mul, mul_comm, pow_mul,
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one, one_pow]

/-- A common divisor of two distinct FLT case I factors divides
`(ζ - 1) · b` (up to associates). -/
theorem dvd_zeta_sub_one_mul_of_dvd_fltCaseI_factors
    (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {η₁ η₂ : K}
    (hη₁ : η₁ ∈ Polynomial.nthRootsFinset p (1 : K))
    (hη₂ : η₂ ∈ Polynomial.nthRootsFinset p (1 : K))
    (hdiff : η₁ ≠ η₂) (b : K) :
    Associated ((η₁ - η₂) * b)
      ((IsCyclotomicExtension.zeta p ℚ K - 1) * b) :=
  ((nthRootsFinset_pairwise_associated_sub p K hη₁ hη₂ hdiff).symm).mul_right b

/-- **`p ∤ (a + b)` from FLT case I.** From `a^p + b^p = c^p` with
`p ∤ c`, deduce `p ∤ (a + b)`. Uses Fermat's little theorem
`x^p ≡ x (mod p)` to reduce `a^p + b^p ≡ a + b (mod p)` and
`c^p ≡ c (mod p)`. -/
theorem fltCaseI_p_not_dvd_add (p : ℕ) [hp : Fact p.Prime]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p) (hc : ¬ (p : ℤ) ∣ c) :
    ¬ (p : ℤ) ∣ (a + b) := by
  intro hab
  apply hc
  -- a + b ≡ c (mod p), and a + b ≡ 0 (mod p), so c ≡ 0 (mod p).
  have hc_mod : (c : ZMod p) = 0 := by
    have hpow_a : ((a : ZMod p)) ^ p = (a : ZMod p) := ZMod.pow_card _
    have hpow_b : ((b : ZMod p)) ^ p = (b : ZMod p) := ZMod.pow_card _
    have hpow_c : ((c : ZMod p)) ^ p = (c : ZMod p) := ZMod.pow_card _
    have h_eq : ((a ^ p + b ^ p : ℤ) : ZMod p) = ((c ^ p : ℤ) : ZMod p) := by
      rw [heq]
    push_cast at h_eq
    rw [hpow_a, hpow_b, hpow_c] at h_eq
    have hab_zero : (a : ZMod p) + (b : ZMod p) = 0 := by
      have h0 : ((a + b : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hab
      push_cast at h0
      exact h0
    rw [hab_zero] at h_eq
    exact h_eq.symm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc_mod

/-- **FLT case I factor coprimality contradiction.**
Under FLT case I conditions (`a^p + b^p = c^p`, `p ∤ abc`, `gcd a b = 1`),
no prime `𝔮 : 𝓞 K` can divide both `(a + ζ^k · b)` and `(a + ζ^l · b)` for
`k ≠ l ∈ [0, p)`. -/
theorem fltCaseI_factor_no_common_prime
    (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k l : ℕ} (hk : k < p) (hl : l < p) (hkl : k ≠ l)
    {𝔮 : 𝓞 K} (hq_prime : Prime 𝔮)
    (h1 : 𝔮 ∣ ((a : 𝓞 K) +
      (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)))
    (h2 : 𝔮 ∣ ((a : 𝓞 K) +
      (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l * (b : 𝓞 K))) :
    False := by
  classical
  -- Step 1: 𝔮 divides the difference (ζ^k - ζ^l) · b
  have h_sub : 𝔮 ∣ ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l) * (b : 𝓞 K) := by
    rw [← fltCaseI_factor_sub_intForm p K a b k l]
    exact dvd_sub h1 h2
  -- Step 2: ζ^k ≠ ζ^l (since k ≠ l < p, and ζ has order p)
  have hne : (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k ≠
      (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l := fun hcontra =>
    hkl <| (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_inj hk hl hcontra
  -- Step 3: (ζ^k - ζ^l) ~ (ζ - 1)
  have hassoc : Associated
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k -
       (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l) :=
    nthRootsFinset_pairwise_associated_sub_intForm p K
      (zeta_pow_mem_nthRootsFinset p K k) (zeta_pow_mem_nthRootsFinset p K l) hne
  -- Step 4: 𝔮 ∣ (ζ - 1) · b
  have h_zsub_b : 𝔮 ∣ ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1) *
      (b : 𝓞 K) :=
    (hassoc.mul_right (b : 𝓞 K)).dvd_iff_dvd_right.mpr h_sub
  -- Step 5: 𝔮 prime ⇒ 𝔮 ∣ (ζ - 1) or 𝔮 ∣ b
  rcases hq_prime.dvd_or_dvd h_zsub_b with h_zsub | h_b
  · -- Case 𝔮 ∣ (ζ - 1): then (ζ - 1) ∣ (a + ζ^k b), so p ∣ (a + b), contradicting case I.
    have h_zsub_dvd : (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 ∣
        ((a : 𝓞 K) + (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k *
          (b : 𝓞 K)) := by
      -- (ζ - 1) is prime, 𝔮 prime divides it, so they're associates
      have hzeta_prime : Prime
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1) :=
        (IsCyclotomicExtension.zeta_spec p ℚ K).zeta_sub_one_prime'
      exact (hq_prime.associated_of_dvd hzeta_prime h_zsub).symm.dvd.trans h1
    rw [zetaSubOne_dvd_factor_iff_p_dvd] at h_zsub_dvd
    -- p ∣ (a + b) contradicts fltCaseI_p_not_dvd_add
    exact (fltCaseI_p_not_dvd_add p heq hc) h_zsub_dvd
  · -- Case 𝔮 ∣ b: then 𝔮 ∣ a, contradicting IsCoprime a b.
    have h_a : 𝔮 ∣ ((a : 𝓞 K)) :=
      dvd_intCast_of_dvd_factor_and_intCast p K a b k h1 h_b
    -- IsCoprime a b ↔ ∃ u v, u*a + v*b = 1; from 𝔮 ∣ a and 𝔮 ∣ b derive 𝔮 ∣ 1
    obtain ⟨u, v, huv⟩ := hab
    have h_one : 𝔮 ∣ ((1 : 𝓞 K)) := by
      have huv_cast : ((u : 𝓞 K)) * (a : 𝓞 K) + (v : 𝓞 K) * (b : 𝓞 K) = 1 := by
        exact_mod_cast huv
      rw [← huv_cast]
      exact dvd_add (h_a.mul_left _) (h_b.mul_left _)
    exact hq_prime.not_unit (isUnit_of_dvd_one h_one)

/-- **FLT case I ideal coprimality** (prime-ideal form).
Under FLT case I conditions, no nonzero prime ideal of `𝓞 K` contains both
`(a + ζ^k · b)` and `(a + ζ^l · b)` for `k ≠ l ∈ [0, p)`. -/
theorem fltCaseI_factor_no_common_prime_ideal
    (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k l : ℕ} (hk : k < p) (hl : l < p) (hkl : k ≠ l)
    {𝔓 : Ideal (𝓞 K)} (h𝔓_prime : 𝔓.IsPrime) (h𝔓_ne : 𝔓 ≠ ⊥)
    (h1 : ((a : 𝓞 K) + (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k *
      (b : 𝓞 K)) ∈ 𝔓)
    (h2 : ((a : 𝓞 K) + (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l *
      (b : 𝓞 K)) ∈ 𝔓) :
    False := by
  -- (ζ^k - ζ^l) · b ∈ 𝔓 (difference of the two factors).
  have h_sub : ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k -
      (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l) * (b : 𝓞 K) ∈ 𝔓 := by
    rw [← fltCaseI_factor_sub_intForm p K a b k l]
    exact 𝔓.sub_mem h1 h2
  -- 𝔓 prime ⇒ (ζ^k - ζ^l) ∈ 𝔓 or b ∈ 𝔓
  rcases h𝔓_prime.mem_or_mem h_sub with h_zsub | h_b
  · -- (ζ^k - ζ^l) ∈ 𝔓; (ζ^k - ζ^l) ~ (ζ - 1), so (ζ - 1) ∈ 𝔓.
    have hne : (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k ≠
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l := fun hcontra =>
      hkl <| (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_inj hk hl hcontra
    have hassoc : Associated
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k -
         (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l) :=
      nthRootsFinset_pairwise_associated_sub_intForm p K
        (zeta_pow_mem_nthRootsFinset p K k) (zeta_pow_mem_nthRootsFinset p K l) hne
    have h_zsub_one : (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 ∈ 𝔓 :=
      (Ideal.mem_iff_of_associated (I := 𝔓) hassoc).mpr h_zsub
    -- Since (ζ - 1) ∈ 𝔓 and (a + ζ^k b) ∈ 𝔓, derive ((a + b) : 𝓞 K) ∈ 𝔓.
    have h_ab : ((a + b : ℤ) : 𝓞 K) ∈ 𝔓 := by
      have h_diff : ((a : 𝓞 K) +
          (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)) -
          ((a + b : ℤ) : 𝓞 K) ∈ 𝔓 := by
        have h_dvd := zetaSubOne_dvd_factor_sub_sum p K a b k
        obtain ⟨η, hη⟩ := h_dvd
        rw [hη]
        exact 𝔓.mul_mem_right _ h_zsub_one
      have h_eq : ((a + b : ℤ) : 𝓞 K) = ((a : 𝓞 K) +
          (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)) -
          (((a : 𝓞 K) +
          (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)) -
          ((a + b : ℤ) : 𝓞 K)) := by ring
      rw [h_eq]
      exact 𝔓.sub_mem h1 h_diff
    -- `zetaPrime ⊆ 𝔓`, and `zetaPrime` is maximal (Dedekind), so `𝔓 = zetaPrime`.
    -- Then `a + b ∈ 𝔓 = zetaPrime`, i.e. `(ζ - 1) ∣ (a + b)`, i.e. `p ∣ (a + b)`.
    have h_span_sub : BernoulliRegular.zetaPrime p K ≤ 𝔓 := by
      rw [BernoulliRegular.zetaPrime, Ideal.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      change (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 ∈ 𝔓 at h_zsub_one
      exact h_zsub_one
    have h_zsub_dvd_ab :
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 ∣ ((a + b : ℤ) : 𝓞 K) := by
      have hzp_max : (BernoulliRegular.zetaPrime p K).IsMaximal := by
        haveI := BernoulliRegular.zetaPrime_isPrime p K
        exact Ring.DimensionLEOne.maximalOfPrime
          (BernoulliRegular.zetaPrime_ne_bot p K) inferInstance
      have h𝔓_max : 𝔓.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔓_ne h𝔓_prime
      have hP_eq : 𝔓 = BernoulliRegular.zetaPrime p K :=
        ((hzp_max.eq_of_le h𝔓_prime.ne_top h_span_sub).symm)
      rw [hP_eq] at h_ab
      rw [← BernoulliRegular.FLT37.span_zetaSubOne_eq_zetaPrime] at h_ab
      exact Ideal.mem_span_singleton.mp h_ab
    have hp_dvd_ab : (p : ℤ) ∣ (a + b) :=
      (zetaSubOne_dvd_intCast_iff p K (a + b)).mp h_zsub_dvd_ab
    exact (fltCaseI_p_not_dvd_add p heq hc) hp_dvd_ab
  · -- b ∈ 𝔓; combined with (a + ζ^k b) ∈ 𝔓, get a ∈ 𝔓; then IsCoprime a b ⇒ 𝔓 = ⊤.
    have h_zb : (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K) ∈ 𝔓 :=
      𝔓.mul_mem_left _ h_b
    have h_a : ((a : 𝓞 K)) ∈ 𝔓 := by
      have := 𝔓.sub_mem h1 h_zb
      simpa using this
    -- IsCoprime a b ⇒ Ideal.span {a, b} = ⊤; in 𝓞 K it's still ⊤ via cast.
    obtain ⟨u, v, huv⟩ := hab
    have huv_cast : ((u : 𝓞 K)) * (a : 𝓞 K) + (v : 𝓞 K) * (b : 𝓞 K) = 1 := by
      exact_mod_cast huv
    have h_one : (1 : 𝓞 K) ∈ 𝔓 := by
      rw [← huv_cast]
      exact 𝔓.add_mem (𝔓.mul_mem_left _ h_a) (𝔓.mul_mem_left _ h_b)
    exact h𝔓_prime.ne_top (𝔓.eq_top_of_isUnit_mem h_one isUnit_one)

/-- **FLT case I principal ideal coprimality.**
Under FLT case I conditions, the principal ideals
`Ideal.span {(a + ζ^k · b)}` and `Ideal.span {(a + ζ^l · b)}` are coprime
in `𝓞 K` for `k ≠ l ∈ [0, p)`. -/
theorem fltCaseI_factor_isCoprime
    (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k l : ℕ} (hk : k < p) (hl : l < p) (hkl : k ≠ l) :
    IsCoprime
      (Ideal.span ({(a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)} :
          Set (𝓞 K)))
      (Ideal.span ({(a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ l * (b : 𝓞 K)} :
          Set (𝓞 K))) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  -- By contradiction: if not ⊤, then contained in some maximal ideal 𝔓.
  by_contra h_ne
  obtain ⟨𝔓, h𝔓_max, h_le⟩ := Ideal.exists_le_maximal _ h_ne
  have h𝔓_prime : 𝔓.IsPrime := h𝔓_max.isPrime
  -- 𝔓 maximal in 𝓞 K (which is not a field) ⇒ 𝔓 ≠ ⊥.
  have h𝔓_ne : 𝔓 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h𝔓_max (RingOfIntegers.not_isField K)
  -- Apply the prime-ideal-level coprime contradiction
  apply fltCaseI_factor_no_common_prime_ideal p K heq hc hab hk hl hkl h𝔓_prime h𝔓_ne
  · exact h_le (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr dvd_rfl))
  · exact h_le (Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr dvd_rfl))

/-- **FLT case I starting equation.** For `(a, b, c) : ℤ` with `a^p + b^p = c^p`
and odd prime `p`, the cyclotomic factorization holds in `K = ℚ(ζ_p)`:
`c^p = ∏_{ζ p-th root of 1} (a + ζ · b)`. -/
theorem fltCaseI_factorization (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a b c : ℤ) (heq : a ^ p + b ^ p = c ^ p) :
    ((c : K)) ^ p =
      ∏ ζ ∈ Polynomial.nthRootsFinset p (1 : K), ((a : K) + ζ * (b : K)) := by
  rw [← pow_add_pow_eq_prod_zeta_mul p hp_odd K (a : K) (b : K)]
  exact_mod_cast heq.symm

/-- **FLT case I starting equation, range-indexed form.** Same as
`fltCaseI_factorization` but indexed by `Finset.range p` via `k ↦ ζ^k`. -/
theorem fltCaseI_factorization_range (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a b c : ℤ) (heq : a ^ p + b ^ p = c ^ p) :
    ((c : K)) ^ p =
      ∏ k ∈ Finset.range p,
        ((a : K) + (IsCyclotomicExtension.zeta p ℚ K) ^ k * (b : K)) := by
  classical
  rw [fltCaseI_factorization p hp_odd K a b c heq, nthRootsFinset_eq_image_range]
  rw [Finset.prod_image]
  intro k₁ hk₁ k₂ hk₂ hkeq
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  exact hζ.pow_inj (Finset.mem_range.mp hk₁) (Finset.mem_range.mp hk₂) hkeq

/-- **FLT case I factorization in 𝓞 K.** For integers `(a, b, c)` with
`a^p + b^p = c^p`, the cyclotomic factorization
`(c : 𝓞 K)^p = ∏ k ∈ Finset.range p, (a + ζ^k · b)` holds in `𝓞 K`. -/
theorem fltCaseI_factorization_ringOfIntegers (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a b c : ℤ) (heq : a ^ p + b ^ p = c ^ p) :
    ((c : 𝓞 K)) ^ p =
      ∏ k ∈ Finset.range p,
        ((a : 𝓞 K) +
          (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)) := by
  apply RingOfIntegers.ext
  push_cast
  exact fltCaseI_factorization_range p hp_odd K a b c heq

/-- **Ideal-level FLT case I factorization.** From `a^p + b^p = c^p`,
the principal ideal equation
`(c)^p = ∏ k ∈ Finset.range p, (a + ζ^k · b)`
holds in `Ideal (𝓞 K)`. -/
theorem fltCaseI_factorization_ideal (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (a b c : ℤ) (heq : a ^ p + b ^ p = c ^ p) :
    (Ideal.span ({(c : 𝓞 K)} : Set (𝓞 K))) ^ p =
      ∏ k ∈ Finset.range p,
        Ideal.span ({(a : 𝓞 K) +
          (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k *
            (b : 𝓞 K)} : Set (𝓞 K)) := by
  rw [Ideal.prod_span_singleton, Ideal.span_singleton_pow]
  congr 1
  rw [Set.singleton_eq_singleton_iff]
  exact fltCaseI_factorization_ringOfIntegers p hp_odd K a b c heq

/-- **Each FLT case I factor's principal ideal is a `p`-th power.**
Combining `fltCaseI_factorization_ideal` (`(c)^p = ∏ (a + ζ^k b)`) with
`fltCaseI_factor_isCoprime` (pairwise coprime), each principal ideal
`Ideal.span {a + ζ^k b}` is a `p`-th power of some ideal of `𝓞 K`.

Uses `Finset.exists_eq_pow_of_mul_eq_pow_of_coprime` on the
`UniqueFactorizationMonoid` structure of `Ideal (𝓞 K)`. -/
theorem fltCaseI_factor_isPrincipal_pow
    (p : ℕ) [hp : Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) {k : ℕ} (hk : k < p) :
    ∃ I : Ideal (𝓞 K),
      Ideal.span ({(a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)} :
          Set (𝓞 K)) = I ^ p := by
  have h_factorization := fltCaseI_factorization_ideal p hp_odd K a b c heq
  have h_coprime : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range p, i ≠ j →
      IsCoprime
        (Ideal.span ({(a : 𝓞 K) +
          (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ i * (b : 𝓞 K)} :
            Set (𝓞 K)))
        (Ideal.span ({(a : 𝓞 K) +
          (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ j * (b : 𝓞 K)} :
            Set (𝓞 K))) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    exact fltCaseI_factor_isCoprime p K heq hc hab hi hj hij
  exact Finset.exists_eq_pow_of_mul_eq_pow_of_coprime h_coprime h_factorization.symm
    k (Finset.mem_range.mpr hk)

/-- **`(I_k)^p` is principal in `𝓞 K`.** From `Ideal.span {a + ζ^k b} = I^p`,
the ideal `I^p` is principal (its generator is `a + ζ^k · b`). -/
theorem fltCaseI_factor_pow_isPrincipal
    (p : ℕ) [hp : Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) {k : ℕ} (hk : k < p) :
    ∃ I : Ideal (𝓞 K), (I ^ p).IsPrincipal ∧
      Ideal.span ({(a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)} :
          Set (𝓞 K)) = I ^ p := by
  obtain ⟨I, hI⟩ := fltCaseI_factor_isPrincipal_pow p hp_odd K heq hc hab hk
  exact ⟨I, hI ▸ ⟨_, rfl⟩, hI⟩

/-- **Under `p` regular** (i.e., `p` coprime to `|Cl(𝓞 K)|`), the ideal `I_k`
underlying `Ideal.span {a + ζ^k · b} = I_k^p` is principal in `𝓞 K`.

This is the standard FLT case I conclusion under regular prime hypothesis:
`a + ζ^k b = u_k γ_k^p` for some unit `u_k` and `γ_k`. -/
theorem fltCaseI_factor_isPrincipal_of_regular
    (p : ℕ) [hp : Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ I : Ideal (𝓞 K), I.IsPrincipal ∧
      Ideal.span ({(a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)} :
          Set (𝓞 K)) = I ^ p := by
  obtain ⟨I, hI_pow_principal, hI⟩ :=
    fltCaseI_factor_pow_isPrincipal p hp_odd K heq hc hab hk
  -- I ≠ ⊥ since `Ideal.span {a + ζ^k · b} ≠ ⊥` (factor is non-zero).
  have h_span_ne : Ideal.span ({(a : 𝓞 K) +
      (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)} :
        Set (𝓞 K)) ≠ ⊥ :=
    fun hbot => h_factor_ne_zero k hk (Ideal.span_singleton_eq_bot.mp hbot)
  have hI_pow_ne : I ^ p ≠ ⊥ := hI ▸ h_span_ne
  have hI_ne : I ≠ ⊥ := fun hbot => hI_pow_ne (by rw [hbot]; exact zero_pow hp.1.ne_zero)
  -- Apply isPrincipal_of_isPrincipal_pow_of_coprime
  exact ⟨I,
    BernoulliRegular.FLT37.isPrincipal_of_isPrincipal_pow_of_coprime h_reg hI_ne hI_pow_principal,
    hI⟩

/-- **The standard FLT case I conclusion under regularity.** From the principal
ideal identity `Ideal.span {a + ζ^k · b} = (Ideal.span {γ})^p`, we extract a unit
`u : (𝓞 K)ˣ` such that `a + ζ^k · b = u · γ^p`. -/
theorem fltCaseI_factor_eq_unit_mul_pow_of_regular
    (p : ℕ) [hp : Fact p.Prime] (hp_odd : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    ∃ (u : (𝓞 K)ˣ) (γ : 𝓞 K),
      ((a : 𝓞 K) +
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)) =
        (u : 𝓞 K) * γ ^ p := by
  obtain ⟨I, hI_principal, hI⟩ :=
    fltCaseI_factor_isPrincipal_of_regular p hp_odd K h_reg heq hc hab
      h_factor_ne_zero hk
  obtain ⟨γ, hγ⟩ := hI_principal
  -- I = Ideal.span {γ}; raise to p-th power and use span_singleton_pow.
  have hI' : Ideal.span ({(a : 𝓞 K) +
      (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K)} :
        Set (𝓞 K)) = Ideal.span ({γ ^ p} : Set (𝓞 K)) := by
    rw [hI, ← Ideal.span_singleton_pow, ← Ideal.submodule_span_eq, ← hγ]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hI'
  refine ⟨u⁻¹, γ, ?_⟩
  -- hu : (a + ζ^k b) * u = γ^p, so a + ζ^k b = u⁻¹ * γ^p.
  rw [← hu, mul_comm ((a : 𝓞 K) +
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ k * (b : 𝓞 K))
    ((u : 𝓞 K)), u.inv_mul_cancel_left]

/-! ## Partial power sum and Ribenboim 1.32 identity

The classical Mirimanoff–Bernoulli connection (Ribenboim, *13 Lectures
on Fermat's Last Theorem*, Lecture VIII identity (1.32)) factors the
Mirimanoff polynomial as

    `(1 - X) · ∑_{k=1}^{p-1} S_e(k) · X^k = mirimanoffPolynomial p (e + 1)`

modulo the `X^p` term `S_e(p - 1) · X^p`, where `S_e(k) = ∑_{j=1}^{k}
j^e` is the partial power sum. This is the structural bridge from the
Mirimanoff polynomial to Bernoulli numbers (via Faulhaber's formula
applied to `S_e(k)`).

The identity is purely algebraic in `(ZMod p)[X]` and does not require
any FLT hypothesis. -/

section PartialPowerSum

/-- The partial power sum `S_e(k) = ∑_{j=1}^{k} (j : ZMod p)^e` viewed
in `ZMod p`. -/
noncomputable def partialPowerSum (p e k : ℕ) : ZMod p :=
  ∑ j ∈ Finset.Ico 1 (k + 1), (j : ZMod p) ^ e

@[simp] theorem partialPowerSum_zero (p e : ℕ) :
    partialPowerSum p e 0 = 0 := by
  simp [partialPowerSum]

theorem partialPowerSum_one (p e : ℕ) :
    partialPowerSum p e 1 = 1 := by
  simp [partialPowerSum]

theorem partialPowerSum_succ (p e k : ℕ) :
    partialPowerSum p e (k + 1) =
      partialPowerSum p e k + ((k + 1 : ℕ) : ZMod p) ^ e := by
  simp only [partialPowerSum, Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]

/-- Difference of consecutive partial power sums recovers the new term. -/
theorem partialPowerSum_sub_partialPowerSum_pred {p e k : ℕ} (hk : 1 ≤ k) :
    partialPowerSum p e k - partialPowerSum p e (k - 1) =
      ((k : ℕ) : ZMod p) ^ e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [partialPowerSum_succ, Nat.succ_sub_one]
  ring

/-- The "Ribenboim 1.32 polynomial" `Q_e(X) = ∑_{k=1}^{p-1} C(S_e(k)) · X^k`
in `(ZMod p)[X]`. -/
noncomputable def partialPowerSumPolynomial (p e : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.Ico 1 p,
    Polynomial.C (partialPowerSum p e k) * Polynomial.X ^ k

/-- Coefficient of `partialPowerSumPolynomial p e` at index `m`:
`partialPowerSum p e m` for `m ∈ [1, p)`, else `0`. -/
theorem partialPowerSumPolynomial_coeff (p : ℕ) [Fact p.Prime] (e m : ℕ) :
    (partialPowerSumPolynomial p e).coeff m =
      if m ∈ Finset.Ico 1 p then partialPowerSum p e m else 0 := by
  unfold partialPowerSumPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hm : m ∈ Finset.Ico 1 p
  · rw [if_pos hm, Finset.sum_eq_single m]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
    · intro k _ hkm
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [Ne.symm hkm]
    · intro hnotmem
      exact absurd hm hnotmem
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hkm : m = k
    · subst hkm; exact absurd hk hm
    · simp [hkm]

/-- **Ribenboim polynomial identity (1.32)** in `(ZMod p)[X]`.

For any natural `e`,
`(1 - X) · ∑_{k=1}^{p-1} C(S_e(k)) · X^k =
  mirimanoffPolynomial p (e + 1) - C(S_e(p - 1)) · X^p`

where `S_e(k) = partialPowerSum p e k`. The `X^p` correction term
vanishes mod `p` whenever `(p - 1) ∤ e` (a Faulhaber consequence —
the relevant range `2 ≤ n ≤ p - 1` for the Mirimanoff use case has
`1 ≤ e ≤ p - 2`, satisfying this divisibility constraint). -/
theorem mirimanoffPolynomial_eq_one_sub_X_mul_partialPowerSumPolynomial
    (p : ℕ) [hp : Fact p.Prime] (e : ℕ) :
    (1 - Polynomial.X) * partialPowerSumPolynomial p e =
      mirimanoffPolynomial p (e + 1) -
        Polynomial.C (partialPowerSum p e (p - 1)) * Polynomial.X ^ p := by
  have hp_two : 2 ≤ p := hp.out.two_le
  -- Reduce to coefficient comparison.
  apply Polynomial.ext
  intro m
  -- Helper: `(X * Q).coeff m`.
  have h_coeff_X_mul :
      (Polynomial.X * partialPowerSumPolynomial p e).coeff m =
        if h : 1 ≤ m then
          if m - 1 ∈ Finset.Ico 1 p then partialPowerSum p e (m - 1) else 0
        else 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · subst hm0
      rw [Polynomial.coeff_X_mul_zero]
      simp
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [Polynomial.coeff_X_mul, partialPowerSumPolynomial_coeff]
      simp
  -- Expand LHS using ring + the coeff-sub form.
  have h_lhs : ((1 - Polynomial.X) * partialPowerSumPolynomial p e).coeff m =
      (partialPowerSumPolynomial p e).coeff m -
        (Polynomial.X * partialPowerSumPolynomial p e).coeff m := by
    rw [show (1 - Polynomial.X : Polynomial (ZMod p)) *
        partialPowerSumPolynomial p e =
        partialPowerSumPolynomial p e -
          Polynomial.X * partialPowerSumPolynomial p e from by ring,
      Polynomial.coeff_sub]
  rw [h_lhs, h_coeff_X_mul, partialPowerSumPolynomial_coeff,
      Polynomial.coeff_sub, mirimanoffPolynomial_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  -- Case split on m relative to [1, p), {p}, > p.
  by_cases hm0 : m = 0
  · subst hm0
    have h0_notin : (0 : ℕ) ∉ Finset.Ico 1 p := by simp [Finset.mem_Ico]
    have h0_notin_iff : ¬ (1 ≤ 0 ∧ 0 < p) := by omega
    have h0_ne_p : (0 : ℕ) ≠ p := by omega
    rw [if_neg h0_notin, dif_neg (by omega : ¬ 1 ≤ 0), if_neg h0_notin_iff, if_neg h0_ne_p]
    simp
  · have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    rw [dif_pos hm_pos]
    by_cases hmp : m < p
    · -- m ∈ [1, p)
      have hm_in : m ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨hm_pos, hmp⟩
      have hm_in_iff : (1 ≤ m ∧ m < p) := ⟨hm_pos, hmp⟩
      have h_mp_ne : m ≠ p := by omega
      rw [if_pos hm_in, if_pos hm_in_iff, if_neg h_mp_ne, mul_zero]
      by_cases hm1 : m = 1
      · subst hm1
        rw [partialPowerSum_one]
        simp
      · have hm_ge_2 : 2 ≤ m := by omega
        have hm_pred_in : m - 1 ∈ Finset.Ico 1 p := by
          rw [Finset.mem_Ico]; omega
        rw [if_pos hm_pred_in, show e + 1 - 1 = e from rfl]
        have h_diff : partialPowerSum p e m - partialPowerSum p e (m - 1) =
            ((m : ℕ) : ZMod p) ^ e :=
          partialPowerSum_sub_partialPowerSum_pred hm_pos
        linear_combination h_diff
    · -- m ≥ p
      push Not at hmp
      have hm_notin : m ∉ Finset.Ico 1 p := by
        rw [Finset.mem_Ico]; omega
      have hm_notin_iff : ¬ (1 ≤ m ∧ m < p) := fun h => absurd h.2 (by omega)
      rw [if_neg hm_notin, if_neg hm_notin_iff]
      by_cases hmp_eq : m = p
      · -- m = p: use rw instead of subst to preserve p in type class
        have hp_pred_in : p - 1 ∈ Finset.Ico 1 p := by
          rw [Finset.mem_Ico]; omega
        rw [hmp_eq, if_pos hp_pred_in, if_pos rfl, mul_one]
      · -- m > p
        have hm_pred_notin : m - 1 ∉ Finset.Ico 1 p := by
          rw [Finset.mem_Ico]; omega
        rw [if_neg hm_pred_notin, if_neg hmp_eq, mul_zero]

end PartialPowerSum
end MirimanoffPolynomial
end FLT37

end BernoulliRegular

end

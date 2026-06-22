module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.FLT37.Principalization
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

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

section MirimanoffSqrt

/-- For `ℓ` prime with `ℓ ≡ 1 (mod 4)`, `-1` is a square in `ZMod ℓ`. -/
theorem isSquare_neg_one_of_mod_four_eq_one (ℓ : ℕ) [Fact ℓ.Prime]
    (h_mod_4 : ℓ % 4 = 1) : IsSquare (-1 : ZMod ℓ) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  omega

/-- For `ℓ` prime with `ℓ ≡ 1 (mod 4)`, a chosen square root of `-1`
in `ZMod ℓ`. This is the **Mirimanoff square root**, a generator (up to
sign) of the order-4 cyclic subgroup of `(ZMod ℓ)ˣ`. -/
noncomputable def mirimanoffSqrt (ℓ : ℕ) [Fact ℓ.Prime]
    (h_mod_4 : ℓ % 4 = 1) : ZMod ℓ :=
  (isSquare_neg_one_of_mod_four_eq_one ℓ h_mod_4).choose

theorem mirimanoffSqrt_sq (ℓ : ℕ) [Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    mirimanoffSqrt ℓ h_mod_4 * mirimanoffSqrt ℓ h_mod_4 = -1 :=
  ((isSquare_neg_one_of_mod_four_eq_one ℓ h_mod_4).choose_spec).symm

/-- The Mirimanoff square root is non-zero. -/
theorem mirimanoffSqrt_ne_zero (ℓ : ℕ) [Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    mirimanoffSqrt ℓ h_mod_4 ≠ 0 := by
  intro h
  have hsq := mirimanoffSqrt_sq ℓ h_mod_4
  rw [h, zero_mul] at hsq
  -- hsq : 0 = -1 in ZMod ℓ
  exact one_ne_zero (neg_eq_zero.mp hsq.symm)

end MirimanoffSqrt

/-! ## Mirimanoff square root as a unit -/

section MirimanoffSqrtUnit

/-- The Mirimanoff square root as a unit in `(ZMod ℓ)ˣ`. -/
noncomputable def mirimanoffSqrtUnit (ℓ : ℕ) [Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    (ZMod ℓ)ˣ :=
  Units.mk0 (mirimanoffSqrt ℓ h_mod_4) (mirimanoffSqrt_ne_zero ℓ h_mod_4)

@[simp]
theorem mirimanoffSqrtUnit_val (ℓ : ℕ) [Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    (mirimanoffSqrtUnit ℓ h_mod_4 : ZMod ℓ) = mirimanoffSqrt ℓ h_mod_4 :=
  rfl

/-- The Mirimanoff square root unit squared is `-1`. -/
theorem mirimanoffSqrtUnit_sq (ℓ : ℕ) [Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    mirimanoffSqrtUnit ℓ h_mod_4 ^ 2 = -1 := by
  apply Units.ext
  simp [pow_two, mirimanoffSqrt_sq]

/-- The Mirimanoff square root unit has fourth power equal to `1`. -/
theorem mirimanoffSqrtUnit_pow_four (ℓ : ℕ) [Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    mirimanoffSqrtUnit ℓ h_mod_4 ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, mirimanoffSqrtUnit_sq]
  exact neg_one_sq

/-- For `ℓ ≡ 1 (mod 4)`, we have `ℓ ≥ 5`. -/
theorem five_le_of_mod_four_eq_one {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    5 ≤ ℓ := by
  have h2 := hℓ.1.two_le
  rcases lt_or_ge ℓ 5 with h | h
  · interval_cases ℓ <;> omega
  · exact h

/-- The Mirimanoff square root unit squared is not `1`: `-1 ≠ 1` in
`ZMod ℓ` for `ℓ ≡ 1 (mod 4)` (which forces `ℓ ≥ 5`). -/
theorem mirimanoffSqrtUnit_sq_ne_one (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    mirimanoffSqrtUnit ℓ h_mod_4 ^ 2 ≠ 1 := by
  rw [mirimanoffSqrtUnit_sq]
  have hℓ5 : 5 ≤ ℓ := five_le_of_mod_four_eq_one h_mod_4
  intro h
  have hne : (-1 : ZMod ℓ) = 1 := by
    have := congrArg Units.val h
    simpa using this
  have h2 : (2 : ZMod ℓ) = 0 := by linear_combination -hne
  rw [show (2 : ZMod ℓ) = ((2 : ℕ) : ZMod ℓ) from by push_cast; rfl,
    ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)

/-- The Mirimanoff square root unit has exact order `4` in `(ZMod ℓ)ˣ`. -/
theorem orderOf_mirimanoffSqrtUnit (ℓ : ℕ) [Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1) :
    orderOf (mirimanoffSqrtUnit ℓ h_mod_4) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (4 : ℕ) = 2 ^ (1 + 1) from by decide]
  apply orderOf_eq_prime_pow
  · change ¬ mirimanoffSqrtUnit ℓ h_mod_4 ^ 2 = 1
    exact mirimanoffSqrtUnit_sq_ne_one ℓ h_mod_4
  · change mirimanoffSqrtUnit ℓ h_mod_4 ^ 4 = 1
    exact mirimanoffSqrtUnit_pow_four ℓ h_mod_4

end MirimanoffSqrtUnit

/-! ## Mirimanoff Galois automorphism -/

section MirimanoffGalAut

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {ℓ} ℚ K]

/-- The **Mirimanoff Galois automorphism** of `K = ℚ(ζ_ℓ)` for
`ℓ ≡ 1 mod 4`. This is the unique element of order 4 in `Gal(K/ℚ)`
corresponding to multiplication by `mirimanoffSqrt ℓ` in `(ZMod ℓ)ˣ`.

It satisfies `mirimanoffGalAut(ζ) = ζ^ω` where `ω² = -1` mod `ℓ`. -/
noncomputable def mirimanoffGalAut : Gal(K/ℚ) :=
  haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
  (IsCyclotomicExtension.Rat.galEquivZMod ℓ K).symm (mirimanoffSqrtUnit ℓ h_mod_4)

/-- The Mirimanoff Galois automorphism has order dividing 4. -/
theorem mirimanoffGalAut_pow_four :
    mirimanoffGalAut ℓ h_mod_4 K ^ 4 = 1 := by
  haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
  rw [mirimanoffGalAut, ← map_pow, mirimanoffSqrtUnit_pow_four, map_one]

/-- The Mirimanoff Galois automorphism squared is not the identity. -/
theorem mirimanoffGalAut_sq_ne_one :
    mirimanoffGalAut ℓ h_mod_4 K ^ 2 ≠ 1 := by
  haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
  intro h
  have h2 : mirimanoffSqrtUnit ℓ h_mod_4 ^ 2 = 1 := by
    have := congrArg (IsCyclotomicExtension.Rat.galEquivZMod ℓ K) h
    rwa [map_pow, mirimanoffGalAut, MulEquiv.apply_symm_apply, map_one] at this
  exact mirimanoffSqrtUnit_sq_ne_one ℓ h_mod_4 h2

/-- Squaring the Mirimanoff Galois automorphism gives the unique
order-2 element of `Gal(K/ℚ)`, i.e., complex conjugation (sending
`ζ ↦ ζ^{-1}`). -/
theorem mirimanoffGalAut_sq_eq_neg_one :
    haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
    IsCyclotomicExtension.Rat.galEquivZMod ℓ K
        (mirimanoffGalAut ℓ h_mod_4 K ^ 2) = -1 := by
  haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
  rw [mirimanoffGalAut, ← map_pow, MulEquiv.apply_symm_apply,
    mirimanoffSqrtUnit_sq]

/-- The square of the Mirimanoff Galois automorphism is exactly
complex conjugation. For `ℓ ≡ 1 mod 4` we have `ℓ ≠ 2`, so the unique
order-2 element of `Gal(K/ℚ)` is complex conjugation. -/
theorem mirimanoffGalAut_sq_eq_complexConjRat [IsCMField K] :
    mirimanoffGalAut ℓ h_mod_4 K ^ 2 =
      BernoulliRegular.complexConjRat (p := ℓ) (K := K)
        (by omega : (ℓ : ℕ) ≠ 2) := by
  haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
  apply (IsCyclotomicExtension.Rat.galEquivZMod ℓ K).injective
  rw [mirimanoffGalAut_sq_eq_neg_one,
    BernoulliRegular.galEquivZMod_complexConj_eq_neg_one]

/-- `galEquivZMod ℓ K (mirimanoffGalAut ℓ h_mod_4 K) = mirimanoffSqrtUnit ℓ h_mod_4`. -/
theorem galEquivZMod_mirimanoffGalAut :
    haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
    IsCyclotomicExtension.Rat.galEquivZMod ℓ K (mirimanoffGalAut ℓ h_mod_4 K) =
      mirimanoffSqrtUnit ℓ h_mod_4 := by
  haveI : NeZero ℓ := ⟨hℓ.1.ne_zero⟩
  rw [mirimanoffGalAut, MulEquiv.apply_symm_apply]

/-- The order of `mirimanoffGalAut` in `Gal(K/ℚ)` is exactly 4. -/
theorem orderOf_mirimanoffGalAut :
    orderOf (mirimanoffGalAut ℓ h_mod_4 K) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_eq_four : (4 : ℕ) = 2 ^ (1 + 1) := by decide
  rw [h_eq_four]
  apply orderOf_eq_prime_pow
  · change ¬ mirimanoffGalAut ℓ h_mod_4 K ^ 2 = 1
    exact mirimanoffGalAut_sq_ne_one ℓ h_mod_4 K
  · change mirimanoffGalAut ℓ h_mod_4 K ^ 4 = 1
    exact mirimanoffGalAut_pow_four ℓ h_mod_4 K

/-- The cyclic subgroup generated by `mirimanoffGalAut` has 4 elements. -/
theorem nat_card_zpowers_mirimanoffGalAut :
    Nat.card (Subgroup.zpowers (mirimanoffGalAut ℓ h_mod_4 K)) = 4 := by
  rw [Nat.card_zpowers, orderOf_mirimanoffGalAut]

/-- Complex conjugation lies in the cyclic subgroup generated by
`mirimanoffGalAut` (specifically, as `mirimanoffGalAut^2`). -/
theorem complexConjRat_mem_zpowers_mirimanoffGalAut [IsCMField K] :
    BernoulliRegular.complexConjRat (p := ℓ) (K := K)
        (by omega : (ℓ : ℕ) ≠ 2) ∈
      Subgroup.zpowers (mirimanoffGalAut ℓ h_mod_4 K) := by
  rw [← mirimanoffGalAut_sq_eq_complexConjRat ℓ h_mod_4 K]
  exact Subgroup.npow_mem_zpowers _ 2

end MirimanoffGalAut

/-! ## Mirimanoff polynomial

Vandiver's Case I uses the **Mirimanoff polynomials**
`φ_n(t) = ∑_{k=1}^{p-1} k^{n-1} t^k` viewed in `(ZMod p)[X]`. The key
congruences relate `φ_n(t)` for various `n` to the FLT solutions
`a^p + b^p = c^p` modulo `p`. -/

section MirimanoffPolynomial

/-- The **Mirimanoff polynomial** of degree-bounded-by-`p` and weight `n`,
viewed in `(ZMod p)[X]`. Defined as `∑_{k=1}^{p-1} k^{n-1} X^k`. -/
noncomputable def mirimanoffPolynomial (p : ℕ) (n : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.Ico 1 p, Polynomial.C ((k : ZMod p) ^ (n - 1)) * Polynomial.X ^ k

/-- A natural number strictly between `0` and `p` is nonzero in `ZMod p`. -/
private theorem natCast_ne_zero_of_pos_of_lt {p m : ℕ} (hpos : 0 < m) (hlt : m < p) :
    (m : ZMod p) ≠ 0 := fun h =>
  absurd (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff m p).mp h)) (by omega)

/-- The constant coefficient of `mirimanoffPolynomial p n` is `0`. -/
theorem mirimanoffPolynomial_coeff_zero (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).coeff 0 = 0 := by
  unfold mirimanoffPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk.1
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp [Ne.symm hk_ne]

/-- `X ∣ mirimanoffPolynomial p n` in `(ZMod p)[X]`, since the constant
coefficient vanishes. -/
theorem X_dvd_mirimanoffPolynomial (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.X ∣ mirimanoffPolynomial p n :=
  Polynomial.X_dvd_iff.mpr (mirimanoffPolynomial_coeff_zero p n)

/-- For `k ≥ p`, the `k`-th coefficient of `mirimanoffPolynomial p n`
is `0`. -/
theorem mirimanoffPolynomial_coeff_of_p_le (p : ℕ) [Fact p.Prime] (n k : ℕ)
    (hk : p ≤ k) :
    (mirimanoffPolynomial p n).coeff k = 0 := by
  unfold mirimanoffPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (by omega : k ≠ j), mul_zero]

/-- The support of `mirimanoffPolynomial p n` is contained in `Ico 1 p`. -/
theorem mirimanoffPolynomial_support_subset (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).support ⊆ Finset.Ico 1 p := by
  intro k hk
  rw [Polynomial.mem_support_iff] at hk
  rw [Finset.mem_Ico]
  refine ⟨?_, ?_⟩
  · rw [Nat.one_le_iff_ne_zero]
    intro h
    subst h
    exact hk (mirimanoffPolynomial_coeff_zero p n)
  · by_contra hge
    exact hk (mirimanoffPolynomial_coeff_of_p_le p n k (Nat.le_of_not_lt hge))

/-- For `k ∈ [1, p)`, the `k`-th coefficient of `mirimanoffPolynomial p n`
is `(k : ZMod p) ^ (n - 1)`. -/
theorem mirimanoffPolynomial_coeff_of_mem_Ico (p : ℕ) [Fact p.Prime] (n k : ℕ)
    (hk : k ∈ Finset.Ico 1 p) :
    (mirimanoffPolynomial p n).coeff k = (k : ZMod p) ^ (n - 1) := by
  rw [Finset.mem_Ico] at hk
  unfold mirimanoffPolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
  · intro j hj hjne
    rw [Finset.mem_Ico] at hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [hjne.symm]
  · intro hknotmem
    exfalso
    apply hknotmem
    rw [Finset.mem_Ico]
    exact hk

/-- For `k ∈ Ico 1 p`, the `k`-th coefficient of `φ_n` is non-zero. -/
theorem mirimanoffPolynomial_coeff_ne_zero_of_mem_Ico
    (p : ℕ) [hp : Fact p.Prime] (n k : ℕ) (hk : k ∈ Finset.Ico 1 p) :
    (mirimanoffPolynomial p n).coeff k ≠ 0 := by
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n k hk]
  apply pow_ne_zero
  rw [Finset.mem_Ico] at hk
  exact natCast_ne_zero_of_pos_of_lt (by omega) hk.2

/-- Coefficient of `φ_n` at index `1` is `1` (for `p ≥ 2`). -/
theorem mirimanoffPolynomial_coeff_one (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).coeff 1 = 1 := by
  have h2le : 2 ≤ p := hp.1.two_le
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n 1 (Finset.mem_Ico.mpr ⟨le_refl _, h2le⟩)]
  rw [Nat.cast_one, one_pow]

/-- Coefficient of `φ_n` at index `2` is `2^(n-1)` (for `p ≥ 3`). -/
theorem mirimanoffPolynomial_coeff_two (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hp_three : 3 ≤ p) :
    (mirimanoffPolynomial p n).coeff 2 = (2 : ZMod p) ^ (n - 1) := by
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n 2
    (Finset.mem_Ico.mpr ⟨by omega, hp_three⟩)]
  push_cast
  rfl

/-- Coefficient of `φ_n` at index `p - 2` is `(-2)^(n-1)` (for `p ≥ 3`). -/
theorem mirimanoffPolynomial_coeff_p_sub_two (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hp_three : 3 ≤ p) :
    (mirimanoffPolynomial p n).coeff (p - 2) = (-2 : ZMod p) ^ (n - 1) := by
  have h_in : p - 2 ∈ Finset.Ico 1 p :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n (p - 2) h_in]
  congr 1
  rw [Nat.cast_sub (by omega : 2 ≤ p), ZMod.natCast_self, zero_sub]
  push_cast
  rfl

/-- Coefficient of `φ_n` at index `3` is `3^(n-1)` (for `p ≥ 5`). -/
theorem mirimanoffPolynomial_coeff_three (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hp_five : 5 ≤ p) :
    (mirimanoffPolynomial p n).coeff 3 = (3 : ZMod p) ^ (n - 1) := by
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n 3
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
  push_cast
  rfl

/-- Coefficient of `φ_n` at index `4` is `4^(n-1)` (for `p ≥ 7`). -/
theorem mirimanoffPolynomial_coeff_four (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hp_seven : 7 ≤ p) :
    (mirimanoffPolynomial p n).coeff 4 = (4 : ZMod p) ^ (n - 1) := by
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n 4
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
  push_cast
  rfl

/-- Coefficient of `φ_n` at index `p - 3` is `(-3)^(n-1)` (for `p ≥ 5`). -/
theorem mirimanoffPolynomial_coeff_p_sub_three (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hp_five : 5 ≤ p) :
    (mirimanoffPolynomial p n).coeff (p - 3) = (-3 : ZMod p) ^ (n - 1) := by
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n (p - 3)
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
  congr 1
  rw [Nat.cast_sub (by omega : 3 ≤ p), ZMod.natCast_self]
  push_cast
  ring

/-- Coefficient of `φ_n` at index `p - 4` is `(-4)^(n-1)` (for `p ≥ 7`). -/
theorem mirimanoffPolynomial_coeff_p_sub_four (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hp_seven : 7 ≤ p) :
    (mirimanoffPolynomial p n).coeff (p - 4) = (-4 : ZMod p) ^ (n - 1) := by
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n (p - 4)
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
  congr 1
  rw [Nat.cast_sub (by omega : 4 ≤ p), ZMod.natCast_self]
  push_cast
  ring

/-- The support of `mirimanoffPolynomial p n` equals `Ico 1 p`. -/
theorem mirimanoffPolynomial_support (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).support = Finset.Ico 1 p := by
  apply Finset.Subset.antisymm (mirimanoffPolynomial_support_subset p n)
  intro k hk
  rw [Polynomial.mem_support_iff]
  exact mirimanoffPolynomial_coeff_ne_zero_of_mem_Ico p n k hk

/-- The cardinality of the support of `φ_n` is `p - 1`. -/
theorem mirimanoffPolynomial_card_support (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).support.card = p - 1 := by
  rw [mirimanoffPolynomial_support, Nat.card_Ico]

/-- The full coefficient characterization: `(φ_n).coeff k = k^(n-1)` for
`1 ≤ k < p`, and `0` otherwise. -/
theorem mirimanoffPolynomial_coeff (p : ℕ) [Fact p.Prime] (n k : ℕ) :
    (mirimanoffPolynomial p n).coeff k =
      if 1 ≤ k ∧ k < p then (k : ZMod p) ^ (n - 1) else 0 := by
  by_cases hk_zero : k = 0
  · subst hk_zero
    rw [mirimanoffPolynomial_coeff_zero]
    rw [if_neg]
    omega
  by_cases hk_lt : k < p
  · rw [if_pos ⟨Nat.one_le_iff_ne_zero.mpr hk_zero, hk_lt⟩]
    exact mirimanoffPolynomial_coeff_of_mem_Ico p n k
      (Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hk_zero, hk_lt⟩)
  · rw [if_neg (fun h => hk_lt h.2)]
    exact mirimanoffPolynomial_coeff_of_p_le p n k (by omega)

theorem mirimanoffPolynomial_eval_zero (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).eval 0 = 0 := by
  unfold mirimanoffPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk_pos : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk.1
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow hk_pos, mul_zero]

theorem mirimanoffPolynomial_natDegree_le (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).natDegree ≤ p - 1 := by
  unfold mirimanoffPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  omega

/-- Evaluating the Mirimanoff polynomial at `t : ZMod p` yields the
expected explicit sum. -/
theorem mirimanoffPolynomial_eval (p : ℕ) [Fact p.Prime] (n : ℕ) (t : ZMod p) :
    (mirimanoffPolynomial p n).eval t =
      ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ (n - 1) * t ^ k := by
  unfold mirimanoffPolynomial
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluating `mirimanoffPolynomial p n` at `t = 1` simplifies to a
straight sum of powers `∑_{k=1}^{p-1} k^{n-1}`. -/
theorem mirimanoffPolynomial_eval_one_eq_sum (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).eval 1 =
      ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ (n - 1) := by
  rw [mirimanoffPolynomial_eval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one]

/-- Evaluating `mirimanoffPolynomial p n` at `t = -1` is the alternating
sum `∑_{k=1}^{p-1} (-1)^k · k^{n-1}`. -/
theorem mirimanoffPolynomial_eval_neg_one_eq_sum (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).eval (-1) =
      ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ (n - 1) * (-1) ^ k := by
  rw [mirimanoffPolynomial_eval]

/-- The k ↔ p - k symmetry of φ_n(-1): in ZMod p, for `n ≥ 1`,
`φ_n(-1) = (-1)^n · φ_n(-1)`. -/
theorem mirimanoffPolynomial_eval_neg_one_symmetry (p : ℕ) [hp : Fact p.Prime]
    (hp_odd : Odd p) {n : ℕ} (hn : 1 ≤ n) :
    (mirimanoffPolynomial p n).eval (-1) =
      (-1) ^ n * (mirimanoffPolynomial p n).eval (-1) := by
  rw [mirimanoffPolynomial_eval_neg_one_eq_sum, Finset.mul_sum]
  refine (Finset.sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Ico] at hk ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Ico] at hk ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Ico] at hk
    omega
  · intro k hk
    simp only [Finset.mem_Ico] at hk
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have hpk : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
      push_cast [Nat.cast_sub (le_of_lt hk.2)]
      rw [ZMod.natCast_self]
      ring
    rw [hpk]
    have hodd : (-1 : ZMod p) ^ p = -1 := Odd.neg_one_pow hp_odd
    have hpkpow : (-1 : ZMod p) ^ (p - k) = -(-1) ^ k := by
      have hk_le : k ≤ p := le_of_lt hk.2
      have hprod : (-1 : ZMod p) ^ (p - k) * (-1) ^ k = -1 := by
        rw [← pow_add, Nat.sub_add_cancel hk_le, hodd]
      have hmul : ((-1 : ZMod p) ^ (p - k) * (-1) ^ k) * (-1) ^ k =
          -1 * (-1) ^ k := by rw [hprod]
      have hsq : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm]
        exact Even.neg_one_pow ⟨k, by ring⟩
      rw [mul_assoc, ← sq, hsq, mul_one, neg_one_mul] at hmul
      exact hmul
    rw [hpkpow, neg_pow]
    have hn_pow : (-1 : ZMod p) ^ n = -1 * (-1) ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm]
      rw [pow_succ]
      ring
    rw [hn_pow]
    ring

/-- **φ_n(-1) vanishes for odd n** (and odd prime p). The symmetry
`φ_n(-1) = (-1)^n · φ_n(-1)` for n odd gives `φ_n(-1) = -φ_n(-1)`,
i.e., `2 · φ_n(-1) = 0`, hence `φ_n(-1) = 0` in ZMod p. -/
theorem mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd (p : ℕ) [hp : Fact p.Prime]
    (hp_odd : Odd p) {n : ℕ} (hn : 1 ≤ n) (hn_odd : Odd n) :
    (mirimanoffPolynomial p n).eval (-1) = 0 := by
  have hsym := mirimanoffPolynomial_eval_neg_one_symmetry p hp_odd hn
  have hneg : (-1 : ZMod p) ^ n = -1 := Odd.neg_one_pow hn_odd
  rw [hneg, neg_one_mul] at hsym
  have h2 : (2 : ZMod p) * (mirimanoffPolynomial p n).eval (-1) = 0 := by
    linear_combination hsym
  have hp_two : 2 ≤ p := hp.1.two_le
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by push_cast; rfl,
      ZMod.natCast_eq_zero_iff] at h
    have : p ≤ 2 := Nat.le_of_dvd (by omega) h
    obtain ⟨m, hm⟩ := hp_odd
    omega
  exact (mul_eq_zero.mp h2).resolve_left h2_ne

/-- The weight-`1` Mirimanoff polynomial is `φ_1(X) = ∑_{k=1}^{p-1} X^k`,
the sum of all positive-degree monomials below `X^p`. -/
theorem mirimanoffPolynomial_one (p : ℕ) [Fact p.Prime] :
    mirimanoffPolynomial p 1 =
      ∑ k ∈ Finset.Ico 1 p, Polynomial.X ^ k := by
  unfold mirimanoffPolynomial
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, Polynomial.C_1, one_mul]

/-- Weight `n = 0` and weight `n = 1` give the same Mirimanoff polynomial,
since `0 - 1 = 0 = 1 - 1` in `ℕ` (truncated subtraction). -/
theorem mirimanoffPolynomial_zero (p : ℕ) [Fact p.Prime] :
    mirimanoffPolynomial p 0 = mirimanoffPolynomial p 1 := by
  unfold mirimanoffPolynomial
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/-- **Differential recurrence for Mirimanoff polynomials.** For `n ≥ 1`,
`φ_{n+1}(X) = X · φ_n'(X)` in `(ZMod p)[X]`. -/
theorem mirimanoffPolynomial_succ_eq_X_mul_derivative (p : ℕ) [Fact p.Prime]
    {n : ℕ} (hn : 1 ≤ n) :
    mirimanoffPolynomial p (n + 1) =
      Polynomial.X * (mirimanoffPolynomial p n).derivative := by
  unfold mirimanoffPolynomial
  rw [Polynomial.derivative_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  have hk_pos : 1 ≤ k := hk.1
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
    show n + 1 - 1 = (n - 1) + 1 from by omega, pow_succ]
  rw [Polynomial.C_mul]
  have hX : (Polynomial.X : Polynomial (ZMod p)) ^ k =
      Polynomial.X * Polynomial.X ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk_pos]
  rw [hX]
  ring

/-- **Bijection lemma:** Summing `f(k : ZMod p)` over `k ∈ Ico 1 p`
equals summing `f x` over `x ∈ ZMod p, x ≠ 0`. This is the bijection
`Ico 1 p ≃ (ZMod p) \ {0}` via `Nat.cast`. -/
theorem sum_Ico_natCast_eq_sum_ne_zero {p : ℕ} [hp : Fact p.Prime] {α : Type*}
    [AddCommMonoid α] (f : ZMod p → α) :
    ∑ k ∈ Finset.Ico 1 p, f (k : ZMod p) =
      ∑ x ∈ Finset.univ.erase (0 : ZMod p), f x := by
  classical
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  refine Finset.sum_bij (fun k _ => (k : ZMod p)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_erase]
    exact ⟨natCast_ne_zero_of_pos_of_lt (by omega) hk.2, Finset.mem_univ _⟩
  · intro k₁ hk₁ k₂ hk₂ hcast
    rw [Finset.mem_Ico] at hk₁ hk₂
    have hv₁ : (k₁ : ZMod p).val = k₁ := ZMod.val_natCast_of_lt hk₁.2
    have hv₂ : (k₂ : ZMod p).val = k₂ := ZMod.val_natCast_of_lt hk₂.2
    have h := congrArg ZMod.val hcast
    rw [hv₁, hv₂] at h
    exact h
  · intro x hx
    rw [Finset.mem_erase] at hx
    refine ⟨x.val, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      refine ⟨?_, ZMod.val_lt x⟩
      rw [Nat.one_le_iff_ne_zero]
      intro h
      apply hx.1
      rw [show (0 : ZMod p) = ((0 : ℕ) : ZMod p) from by push_cast; rfl, ← h]
      exact (ZMod.natCast_zmod_val x).symm
    · exact ZMod.natCast_zmod_val x
  · intro k _
    rfl

/-- **Fermat shift for Mirimanoff polynomials.** For `n ≥ 1`,
`φ_{n + (p-1)} = φ_n` in `(ZMod p)[X]`, since `k^{p-1} = 1` for
`k ∈ {1, ..., p-1}`. -/
theorem mirimanoffPolynomial_add_card_sub_one (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : 1 ≤ n) :
    mirimanoffPolynomial p (n + (p - 1)) = mirimanoffPolynomial p n := by
  unfold mirimanoffPolynomial
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  have hk_ne : (k : ZMod p) ≠ 0 := natCast_ne_zero_of_pos_of_lt (by omega) hk.2
  have heq : n + (p - 1) - 1 = (n - 1) + (p - 1) := by omega
  rw [heq, pow_add, ZMod.pow_card_sub_one_eq_one hk_ne, mul_one]

/-- Fermat's little theorem applied to the Mirimanoff polynomial:
`φ_p(t) = ∑_{k=1}^{p-1} t^k`, since `k^{p-1} ≡ 1 (mod p)` for
`1 ≤ k ≤ p-1`. -/
theorem mirimanoffPolynomial_at_p (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p p =
      ∑ k ∈ Finset.Ico 1 p, Polynomial.X ^ k := by
  unfold mirimanoffPolynomial
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  have hk_ne : (k : ZMod p) ≠ 0 := natCast_ne_zero_of_pos_of_lt (by omega) hk.2
  rw [ZMod.pow_card_sub_one_eq_one hk_ne, Polynomial.C_1, one_mul]

/-- `φ_p = φ_1` in `(ZMod p)[X]`, by Fermat's little theorem. -/
theorem mirimanoffPolynomial_at_p_eq_one (p : ℕ) [Fact p.Prime] :
    mirimanoffPolynomial p p = mirimanoffPolynomial p 1 := by
  rw [mirimanoffPolynomial_at_p, mirimanoffPolynomial_one]

/-- Telescoping identity: `φ_p(X) · (X - 1) = X^p - X` in `(ZMod p)[X]`. -/
theorem mirimanoffPolynomial_at_p_mul_X_sub_one (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p p * (Polynomial.X - 1) =
      Polynomial.X ^ p - Polynomial.X := by
  rw [mirimanoffPolynomial_at_p,
    geom_sum_Ico_mul (Polynomial.X : Polynomial (ZMod p)) hp.1.one_lt.le, pow_one]

/-- `φ_p` divides `X^p - X` in `(ZMod p)[X]`. -/
theorem mirimanoffPolynomial_at_p_dvd_X_pow_sub_X (p : ℕ) [Fact p.Prime] :
    mirimanoffPolynomial p p ∣
      (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)) :=
  ⟨Polynomial.X - 1, (mirimanoffPolynomial_at_p_mul_X_sub_one p).symm⟩

/-- The `(p-1)`-th coefficient of `φ_n` is `(-1)^(n-1)`. -/
theorem mirimanoffPolynomial_coeff_card_sub_one (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).coeff (p - 1) = (-1 : ZMod p) ^ (n - 1) := by
  have h2le : 2 ≤ p := hp.1.two_le
  have hp_pos : 0 < p := hp.1.pos
  rw [mirimanoffPolynomial_coeff_of_mem_Ico p n (p - 1)
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
  congr 1
  rw [Nat.cast_sub hp_pos, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- The `(p-1)`-th coefficient of `φ_n` is non-zero (it is `(-1)^(n-1) = ±1`). -/
theorem mirimanoffPolynomial_coeff_card_sub_one_ne_zero (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).coeff (p - 1) ≠ 0 := by
  rw [mirimanoffPolynomial_coeff_card_sub_one p n]
  apply pow_ne_zero
  intro h
  have h1 : (1 : ZMod p) = 0 := by linear_combination -h
  exact one_ne_zero h1

/-- The natDegree of `φ_n` is exactly `p - 1` (for any `n`). -/
theorem mirimanoffPolynomial_natDegree (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).natDegree = p - 1 := by
  exact le_antisymm (mirimanoffPolynomial_natDegree_le p n)
    (Polynomial.le_natDegree_of_ne_zero <| mirimanoffPolynomial_coeff_card_sub_one_ne_zero p n)

/-- `φ_n` is nonzero (for any `n`). -/
theorem mirimanoffPolynomial_ne_zero (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    mirimanoffPolynomial p n ≠ 0 := by
  intro h
  have h_coeff := mirimanoffPolynomial_coeff_card_sub_one_ne_zero p n
  rw [h, Polynomial.coeff_zero] at h_coeff
  exact h_coeff rfl

/-- The polynomial degree of `φ_n` is exactly `p - 1`. -/
theorem mirimanoffPolynomial_degree (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).degree = (p - 1 : ℕ) := by
  rw [Polynomial.degree_eq_natDegree (mirimanoffPolynomial_ne_zero p n),
    mirimanoffPolynomial_natDegree]

/-- The leading coefficient of `φ_n` is `(-1)^(n-1)`. -/
theorem mirimanoffPolynomial_leadingCoeff (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (mirimanoffPolynomial p n).leadingCoeff = (-1 : ZMod p) ^ (n - 1) := by
  rw [Polynomial.leadingCoeff, mirimanoffPolynomial_natDegree p n,
    mirimanoffPolynomial_coeff_card_sub_one]

/-- For odd `n`, `φ_n` is monic. -/
theorem mirimanoffPolynomial_monic_of_odd (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : 1 ≤ n) (hn_odd : Odd n) :
    (mirimanoffPolynomial p n).Monic := by
  rw [Polynomial.Monic, mirimanoffPolynomial_leadingCoeff]
  have hn1_even : Even (n - 1) := by
    rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm] at hn_odd
    exact Nat.not_odd_iff_even.mp ((Nat.odd_add_one).mp hn_odd)
  exact Even.neg_one_pow hn1_even

/-- For even `n ≥ 2`, the leading coefficient of `φ_n` is `-1`. -/
theorem mirimanoffPolynomial_leadingCoeff_of_even (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : 1 ≤ n) (hn_even : Even n) :
    (mirimanoffPolynomial p n).leadingCoeff = -1 := by
  rw [mirimanoffPolynomial_leadingCoeff]
  have hn1_odd : Odd (n - 1) := by
    rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm] at hn_even
    rcases hn_even with ⟨k, hk⟩
    -- n - 1 + 1 = 2 * k
    -- Need: Odd (n - 1)
    refine ⟨k - 1, ?_⟩
    have hk_pos : 1 ≤ k := by omega
    omega
  exact Odd.neg_one_pow hn1_odd

/-- The `(p-1)`-th coefficient of `φ_p` is `1`. -/
theorem mirimanoffPolynomial_at_p_coeff_card_sub_one (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).coeff (p - 1) = 1 := by
  have h2le : 2 ≤ p := hp.1.two_le
  rw [mirimanoffPolynomial_at_p, Polynomial.finsetSum_coeff]
  have hp1 : p - 1 ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  rw [Finset.sum_eq_single (p - 1)]
  · rw [Polynomial.coeff_X_pow_self]
  · intro j hj hj_ne
    rw [Polynomial.coeff_X_pow]
    rw [if_neg (fun h => hj_ne h.symm)]
  · intro hcontra
    exact absurd hp1 hcontra

/-- The `(p-2)`-th coefficient of `φ_p` is `1` (for `p ≥ 3`).
By Vieta, this equals `-(sum of roots) = -(0 - 1) = 1`. -/
theorem mirimanoffPolynomial_at_p_coeff_p_sub_two (p : ℕ) [hp : Fact p.Prime]
    (hp_three : 3 ≤ p) :
    (mirimanoffPolynomial p p).coeff (p - 2) = 1 := by
  rw [mirimanoffPolynomial_coeff_p_sub_two p p (by omega)]
  -- `(-2 : ZMod p) ^ (p - 1) = 1` by Fermat's little theorem
  have h_ne : (-2 : ZMod p) ≠ 0 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by linear_combination -h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by push_cast; rfl,
      ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  exact ZMod.pow_card_sub_one_eq_one h_ne

/-- The `(p-3)`-th coefficient of `φ_p` is `1` (for `p ≥ 5`).
Equals `(-3 : ZMod p)^(p-1) = 1` by Fermat's little theorem. -/
theorem mirimanoffPolynomial_at_p_coeff_p_sub_three (p : ℕ) [hp : Fact p.Prime]
    (hp_five : 5 ≤ p) :
    (mirimanoffPolynomial p p).coeff (p - 3) = 1 := by
  rw [mirimanoffPolynomial_coeff_p_sub_three p p hp_five]
  -- `(-3 : ZMod p) ^ (p - 1) = 1` by Fermat's little theorem
  have h_ne : (-3 : ZMod p) ≠ 0 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by linear_combination -h
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl,
      ZMod.natCast_eq_zero_iff] at h3
    exact absurd (Nat.le_of_dvd (by omega) h3) (by omega)
  exact ZMod.pow_card_sub_one_eq_one h_ne

/-- The `(p-4)`-th coefficient of `φ_p` is `1` (for `p ≥ 7`).
Equals `(-4 : ZMod p)^(p-1) = 1` by Fermat's little theorem. -/
theorem mirimanoffPolynomial_at_p_coeff_p_sub_four (p : ℕ) [hp : Fact p.Prime]
    (hp_seven : 7 ≤ p) :
    (mirimanoffPolynomial p p).coeff (p - 4) = 1 := by
  rw [mirimanoffPolynomial_coeff_p_sub_four p p hp_seven]
  -- `(-4 : ZMod p) ^ (p - 1) = 1` by Fermat's little theorem
  have h_ne : (-4 : ZMod p) ≠ 0 := by
    intro h
    have h4 : (4 : ZMod p) = 0 := by linear_combination -h
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl,
      ZMod.natCast_eq_zero_iff] at h4
    exact absurd (Nat.le_of_dvd (by omega) h4) (by omega)
  exact ZMod.pow_card_sub_one_eq_one h_ne

/-- The `2`nd coefficient of `φ_p` is `1` (for `p ≥ 3`). Equals
`(2 : ZMod p)^(p-1) = 1` by Fermat's little theorem. -/
theorem mirimanoffPolynomial_at_p_coeff_two (p : ℕ) [hp : Fact p.Prime]
    (hp_three : 3 ≤ p) :
    (mirimanoffPolynomial p p).coeff 2 = 1 := by
  rw [mirimanoffPolynomial_coeff_two p p hp_three]
  have h_ne : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by push_cast; rfl]
    exact natCast_ne_zero_of_pos_of_lt (by omega) (by omega)
  exact ZMod.pow_card_sub_one_eq_one h_ne

/-- The `3`rd coefficient of `φ_p` is `1` (for `p ≥ 5`). -/
theorem mirimanoffPolynomial_at_p_coeff_three (p : ℕ) [hp : Fact p.Prime]
    (hp_five : 5 ≤ p) :
    (mirimanoffPolynomial p p).coeff 3 = 1 := by
  rw [mirimanoffPolynomial_coeff_three p p hp_five]
  have h_ne : (3 : ZMod p) ≠ 0 := by
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
    exact natCast_ne_zero_of_pos_of_lt (by omega) (by omega)
  exact ZMod.pow_card_sub_one_eq_one h_ne

/-- The `4`th coefficient of `φ_p` is `1` (for `p ≥ 7`). -/
theorem mirimanoffPolynomial_at_p_coeff_four (p : ℕ) [hp : Fact p.Prime]
    (hp_seven : 7 ≤ p) :
    (mirimanoffPolynomial p p).coeff 4 = 1 := by
  rw [mirimanoffPolynomial_coeff_four p p hp_seven]
  have h_ne : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl]
    exact natCast_ne_zero_of_pos_of_lt (by omega) (by omega)
  exact ZMod.pow_card_sub_one_eq_one h_ne

/-- The `natDegree` of `φ_p` is exactly `p - 1`. -/
theorem mirimanoffPolynomial_at_p_natDegree (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).natDegree = p - 1 := by
  apply le_antisymm (mirimanoffPolynomial_natDegree_le p p)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [mirimanoffPolynomial_at_p_coeff_card_sub_one]
  exact one_ne_zero

/-- `φ_p` is monic. -/
theorem mirimanoffPolynomial_at_p_monic (p : ℕ) [Fact p.Prime] :
    (mirimanoffPolynomial p p).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff,
    mirimanoffPolynomial_at_p_natDegree, mirimanoffPolynomial_at_p_coeff_card_sub_one]

/-- `φ_1` has natDegree `p - 1`, by `φ_p = φ_1`. -/
theorem mirimanoffPolynomial_one_natDegree (p : ℕ) [Fact p.Prime] :
    (mirimanoffPolynomial p 1).natDegree = p - 1 := by
  rw [← mirimanoffPolynomial_at_p_eq_one, mirimanoffPolynomial_at_p_natDegree]

end MirimanoffPolynomial
end FLT37

end BernoulliRegular

end

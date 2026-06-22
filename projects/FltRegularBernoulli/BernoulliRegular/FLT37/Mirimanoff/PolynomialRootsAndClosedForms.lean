module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.FLT37.Principalization
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import BernoulliRegular.FLT37.Mirimanoff.PolynomialDefinition

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

/-- `φ_1` is monic. -/
theorem mirimanoffPolynomial_one_monic (p : ℕ) [Fact p.Prime] :
    (mirimanoffPolynomial p 1).Monic := by
  rw [← mirimanoffPolynomial_at_p_eq_one]
  exact mirimanoffPolynomial_at_p_monic p

/-- `φ_1` is divisible by `X` in `(ZMod p)[X]`. -/
theorem X_dvd_mirimanoffPolynomial_one (p : ℕ) [Fact p.Prime] :
    Polynomial.X ∣ mirimanoffPolynomial p 1 :=
  X_dvd_mirimanoffPolynomial p 1

/-- Evaluating the telescope identity: `φ_p(t) · (t - 1) = t^p - t` in `ZMod p`. -/
theorem mirimanoffPolynomial_at_p_eval_mul (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    (mirimanoffPolynomial p p).eval t * (t - 1) = t ^ p - t := by
  have h := mirimanoffPolynomial_at_p_mul_X_sub_one p
  apply_fun fun q => Polynomial.eval t q at h
  simpa using h

/-- More general telescope: in any ring extension `R` of `ZMod p`,
`φ_p(t) · (t - 1) = t^p - t` for any `t : R`. -/
theorem mirimanoffPolynomial_at_p_aeval_mul (p : ℕ) [Fact p.Prime]
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] (t : R) :
    (mirimanoffPolynomial p p).aeval t * (t - 1) = t ^ p - t := by
  have h := mirimanoffPolynomial_at_p_mul_X_sub_one p
  apply_fun fun q => Polynomial.aeval (R := ZMod p) (A := R) t q at h
  simpa using h

/-- Evaluating any Mirimanoff polynomial via `aeval` at `t : R`
yields the explicit sum in `R`. -/
theorem mirimanoffPolynomial_aeval (p : ℕ) [Fact p.Prime] (n : ℕ)
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] (t : R) :
    (mirimanoffPolynomial p n).aeval t =
      ∑ k ∈ Finset.Ico 1 p,
        algebraMap (ZMod p) R ((k : ZMod p) ^ (n - 1)) * t ^ k := by
  unfold mirimanoffPolynomial
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X_pow]

/-- The aeval form of `mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd`:
in any `(ZMod p)`-algebra `R` of characteristic `p`, for odd prime `p`
and odd weight `n ≥ 1`, evaluating at `-1 ∈ R` gives `0`. -/
theorem mirimanoffPolynomial_aeval_neg_one_eq_zero_of_odd (p : ℕ) [Fact p.Prime]
    (hp_odd : Odd p) {n : ℕ} (hn : 1 ≤ n) (hn_odd : Odd n)
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] :
    (mirimanoffPolynomial p n).aeval (-1 : R) = 0 := by
  have h := mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd p hp_odd hn hn_odd
  have hneg_one : (-1 : R) = algebraMap (ZMod p) R (-1) := by
    rw [map_neg, map_one]
  rw [hneg_one, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, h, map_zero]

/-- Vanishing of `φ_p(t)` for `t ∈ ZMod p \ {1}`: in fact `φ_p(t) = 0`
for all `t ≠ 1` in `ZMod p`, using Fermat's little theorem `t^p = t`. -/
theorem mirimanoffPolynomial_at_p_eval_eq_zero_of_ne_one (p : ℕ) [Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p p).eval t = 0 := by
  have htp : t ^ p = t := ZMod.pow_card t
  have h := mirimanoffPolynomial_at_p_eval_mul p t
  rw [htp, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr ht)

/-- **Vanishing of `φ_1(t)` for `t ∈ ZMod p \ {1}`.** Same as
`mirimanoffPolynomial_at_p_eval_eq_zero_of_ne_one` rewritten using
`φ_p = φ_1` (`mirimanoffPolynomial_at_p_eq_one`). -/
theorem mirimanoffPolynomial_one_eval_eq_zero_of_ne_one (p : ℕ) [Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 1).eval t = 0 := by
  rw [← mirimanoffPolynomial_at_p_eq_one]
  exact mirimanoffPolynomial_at_p_eval_eq_zero_of_ne_one p t ht

/-- **Polynomial identity for `φ_2`.**

In `(ZMod p)[X]`: `φ_2(X) · (X - 1) = -X^p - φ_1(X)`.

Equivalently `φ_2(X) · (1 - X) = X^p + φ_1(X)`. Derived by differentiating
the corresponding identity for `φ_1` (= `φ_p`) using the formal derivative
in `(ZMod p)[X]`. -/
theorem mirimanoffPolynomial_two_mul_X_sub_one (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p 2 * (Polynomial.X - 1) =
      -(Polynomial.X ^ p) - mirimanoffPolynomial p 1 := by
  -- Step 1: φ_1(X) · (X - 1) = X^p - X (from existing φ_p identity).
  have h1 : mirimanoffPolynomial p 1 * (Polynomial.X - 1 : Polynomial (ZMod p)) =
      Polynomial.X ^ p - Polynomial.X := by
    rw [← mirimanoffPolynomial_at_p_eq_one]
    exact mirimanoffPolynomial_at_p_mul_X_sub_one p
  -- Step 2: Differentiate both sides.
  have h2 := congrArg Polynomial.derivative h1
  -- LHS: φ_1' · (X - 1) + φ_1.
  rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_one, sub_zero, mul_one] at h2
  -- RHS: (X^p - X)' = p · X^(p-1) - 1 = -1 in (ZMod p)[X] since p ≡ 0.
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X] at h2
  have hp_zero : (Polynomial.C ((p : ℕ) : ZMod p) : Polynomial (ZMod p)) = 0 := by
    rw [ZMod.natCast_self, Polynomial.C_0]
  rw [hp_zero, zero_mul, zero_sub] at h2
  -- h2 : φ_1' · (X - 1) + φ_1 = -1
  -- Step 3: Multiply by X. φ_2 = X · φ_1' (Euler operator).
  have h3 : Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 1) *
      (Polynomial.X - 1) + Polynomial.X * mirimanoffPolynomial p 1 = -Polynomial.X := by
    have := congrArg (fun q => Polynomial.X * q) h2
    linear_combination this
  have h_euler : mirimanoffPolynomial p 2 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 1) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 1) (le_refl 1)
  rw [← h_euler] at h3
  -- h3 : φ_2 · (X - 1) + X · φ_1 = -X
  -- Step 4: Substitute X · φ_1 = (X-1) · φ_1 + φ_1 = (X^p - X) + φ_1.
  have h_x_phi1 : Polynomial.X * mirimanoffPolynomial p 1 =
      Polynomial.X ^ p - Polynomial.X + mirimanoffPolynomial p 1 := by
    have : Polynomial.X * mirimanoffPolynomial p 1 =
        (Polynomial.X - 1) * mirimanoffPolynomial p 1 + mirimanoffPolynomial p 1 := by ring
    rw [this, mul_comm (Polynomial.X - 1) _, h1]
  rw [h_x_phi1] at h3
  -- h3 : φ_2 · (X - 1) + (X^p - X) + φ_1 = -X
  -- Therefore: φ_2 · (X - 1) = -X - (X^p - X) - φ_1 = -X^p - φ_1.
  linear_combination h3

/-- **Aeval form of the φ_2 polynomial identity.**

In any `(ZMod p)`-algebra `R`, for any `t : R`:
`φ_2(t) · (t - 1) = -t^p - φ_1(t)` (in `R`).

Generalises `mirimanoffPolynomial_two_mul_X_sub_one` from `(ZMod p)[X]`
to any `(ZMod p)`-algebra by applying `aeval`. -/
theorem mirimanoffPolynomial_two_aeval_mul_X_sub_one (p : ℕ) [hp : Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (ZMod p) R] (t : R) :
    (mirimanoffPolynomial p 2).aeval t * (t - 1) =
      -(t ^ p) - (mirimanoffPolynomial p 1).aeval t := by
  have h := mirimanoffPolynomial_two_mul_X_sub_one p
  have h' := congrArg (Polynomial.aeval (R := ZMod p) (A := R) t) h
  simp only [map_mul, map_sub, map_neg, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_one] at h'
  exact h'

/-- **Closed form for `φ_2(t)` at `t ∈ ZMod p \ {1}`.**

For `t ∈ ZMod p` with `t ≠ 1`, `φ_2(t) · (1 - t) = t`. Equivalently
`φ_2(t) = t / (1 - t)`. Derived from `mirimanoffPolynomial_two_mul_X_sub_one`
plus Fermat (`t^p = t`) and `φ_1(t) = 0`. -/
theorem mirimanoffPolynomial_two_eval_mul_one_sub (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 2).eval t * (1 - t) = t := by
  -- Apply the polynomial identity at t.
  have h := mirimanoffPolynomial_two_mul_X_sub_one p
  have h_eval := congrArg (Polynomial.eval t) h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_pow] at h_eval
  -- h_eval : φ_2(t) · (t - 1) = -t^p - φ_1(t)
  have htp : t ^ p = t := ZMod.pow_card t
  have h_phi1 := mirimanoffPolynomial_one_eval_eq_zero_of_ne_one p t ht
  rw [htp, h_phi1] at h_eval
  -- h_eval : φ_2(t) · (t - 1) = -t - 0
  linear_combination -h_eval

/-- **`φ_2(t) ≠ 0` when `t ∉ {0, 1}`.** Since `φ_2(t)·(1-t) = t` and
`1 - t ≠ 0`, we have `φ_2(t) = 0 ↔ t = 0`.

Useful for noting: in FLT case I, `t = -a/b` with `p ∤ a`, so `t ≠ 0`,
hence `φ_2(t) ≠ 0`. The `MirimanoffPolynomialVanishing` predicate's
claim that `φ_2(t) = 0` is therefore not directly derivable from FLT
case I alone. -/
theorem mirimanoffPolynomial_two_eval_ne_zero (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht_zero : t ≠ 0) (ht_one : t ≠ 1) :
    (mirimanoffPolynomial p 2).eval t ≠ 0 := by
  intro hzero
  have h := mirimanoffPolynomial_two_eval_mul_one_sub p t ht_one
  rw [hzero, zero_mul] at h
  exact ht_zero h.symm

/-- **Division form of φ_2 closed form.** For `t ∈ ZMod p` with `t ≠ 1`,
`φ_2(t) = t / (1 - t)`. -/
theorem mirimanoffPolynomial_two_eval_eq_div (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 2).eval t = t / (1 - t) := by
  have h1 := mirimanoffPolynomial_two_eval_mul_one_sub p t ht
  have h_one_sub_ne : (1 - t) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  field_simp
  linear_combination h1

/-- **Polynomial identity for `φ_3`.**

In `(ZMod p)[X]`: `φ_3(X) · (X - 1) = -(X + 1) · φ_2(X)`.

Derived by differentiating the `φ_2` identity, using the Euler operator
`φ_3 = X · φ_2'`. -/
theorem mirimanoffPolynomial_three_mul_X_sub_one (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p 3 * (Polynomial.X - 1) =
      -(Polynomial.X + 1) * mirimanoffPolynomial p 2 := by
  -- Start from φ_2 · (X - 1) = -X^p - φ_1.
  have h1 := mirimanoffPolynomial_two_mul_X_sub_one p
  -- Differentiate.
  have h2 := congrArg Polynomial.derivative h1
  rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_one, sub_zero, mul_one,
      Polynomial.derivative_sub, Polynomial.derivative_neg,
      Polynomial.derivative_X_pow] at h2
  -- (X^p)' = p · X^{p-1} = 0 in (ZMod p)[X].
  have hp_zero : (Polynomial.C ((p : ℕ) : ZMod p) : Polynomial (ZMod p)) = 0 := by
    rw [ZMod.natCast_self, Polynomial.C_0]
  rw [hp_zero, zero_mul, neg_zero, zero_sub] at h2
  -- h2 : φ_2' · (X - 1) + φ_2 = -φ_1'
  -- Multiply by X.
  have h3 : Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 2) *
      (Polynomial.X - 1) + Polynomial.X * mirimanoffPolynomial p 2 =
      Polynomial.X * (-Polynomial.derivative (mirimanoffPolynomial p 1)) := by
    have := congrArg (fun q => Polynomial.X * q) h2
    linear_combination this
  -- Use Euler: φ_3 = X · φ_2', and -X · φ_1' = -(φ_2) (Euler).
  have h_euler_3 : mirimanoffPolynomial p 3 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 2) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 2) (by norm_num : 1 ≤ 2)
  have h_euler_2 : mirimanoffPolynomial p 2 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 1) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 1) (le_refl 1)
  rw [← h_euler_3] at h3
  -- h3 : φ_3 · (X - 1) + X · φ_2 = X · (-φ_1') = -(X · φ_1') = -φ_2
  have h_rhs : Polynomial.X * (-Polynomial.derivative (mirimanoffPolynomial p 1)) =
      -mirimanoffPolynomial p 2 := by
    rw [h_euler_2, mul_neg]
  rw [h_rhs] at h3
  -- h3 : φ_3 · (X - 1) + X · φ_2 = -φ_2
  -- Rearrange: φ_3 · (X - 1) = -φ_2 - X · φ_2 = -(1 + X) · φ_2 = -(X + 1) · φ_2.
  linear_combination h3

/-- **Aeval form of the φ_3 polynomial identity.**

In any `(ZMod p)`-algebra `R`, for any `t : R`:
`φ_3(t) · (t - 1) = -(t + 1) · φ_2(t)` (in `R`).

Generalises `mirimanoffPolynomial_three_mul_X_sub_one` from `(ZMod p)[X]`
to any `(ZMod p)`-algebra. -/
theorem mirimanoffPolynomial_three_aeval_mul_X_sub_one (p : ℕ) [hp : Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (ZMod p) R] (t : R) :
    (mirimanoffPolynomial p 3).aeval t * (t - 1) =
      -(t + 1) * (mirimanoffPolynomial p 2).aeval t := by
  have h := mirimanoffPolynomial_three_mul_X_sub_one p
  have h' := congrArg (Polynomial.aeval (R := ZMod p) (A := R) t) h
  simp only [map_mul, map_sub, map_neg, map_add, Polynomial.aeval_X,
    Polynomial.aeval_one] at h'
  exact h'

/-- **Closed form for `φ_3(t)` at `t ∈ ZMod p \ {1}`.**

For `t ∈ ZMod p` with `t ≠ 1`, `φ_3(t) · (t - 1)² = t · (t + 1)`.
Equivalently `φ_3(t) = t·(t + 1) / (t - 1)²`. Combines
`mirimanoffPolynomial_three_mul_X_sub_one` with the closed form for
`φ_2(t)`. -/
theorem mirimanoffPolynomial_three_eval_mul_X_sub_one_sq (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 3).eval t * (t - 1) ^ 2 = t * (t + 1) := by
  -- From the polynomial identity: φ_3(t) · (t - 1) = -(t + 1) · φ_2(t).
  have h := mirimanoffPolynomial_three_mul_X_sub_one p
  have h_eval := congrArg (Polynomial.eval t) h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_add] at h_eval
  -- h_eval : φ_3(t) · (t - 1) = -(t + 1) · φ_2(t)
  have h2 := mirimanoffPolynomial_two_eval_mul_one_sub p t ht
  -- φ_2(t) · (1 - t) = t, i.e., φ_2(t) · -(t - 1) = t, so φ_2(t) · (t - 1) = -t.
  have h2' : (mirimanoffPolynomial p 2).eval t * (t - 1) = -t := by linear_combination -h2
  -- Multiply h_eval by (t - 1):
  -- φ_3(t) · (t - 1)² = -(t + 1) · φ_2(t) · (t - 1) = -(t + 1) · (-t) = t · (t + 1).
  have := congrArg (fun x => x * (t - 1)) h_eval
  -- this : φ_3(t) · (t - 1) · (t - 1) = -(t + 1) · φ_2(t) · (t - 1)
  rw [show ((-(t + 1)) * (mirimanoffPolynomial p 2).eval t) * (t - 1) =
      (-(t + 1)) * ((mirimanoffPolynomial p 2).eval t * (t - 1)) by ring] at this
  rw [h2'] at this
  linear_combination this

/-- **Division form of φ_3 closed form.** For `t ∈ ZMod p` with `t ≠ 1`,
`φ_3(t) = t · (t + 1) / (t - 1)²`. -/
theorem mirimanoffPolynomial_three_eval_eq_div (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 3).eval t = t * (t + 1) / (t - 1) ^ 2 := by
  have h1 := mirimanoffPolynomial_three_eval_mul_X_sub_one_sq p t ht
  have h_t_sub_one_ne : (t - 1) ≠ 0 := sub_ne_zero.mpr ht
  have h_sq_ne : (t - 1) ^ 2 ≠ 0 := pow_ne_zero _ h_t_sub_one_ne
  field_simp
  linear_combination h1

/-- **`φ_3(t) = 0` implies `t ∈ {0, -1}` for `t ≠ 1`.**

If `φ_3(t) = 0` in `ZMod p` and `t ≠ 1`, then `t = 0` or `t = -1`.
This follows from the closed form `φ_3(t)·(t - 1)² = t·(t + 1)`: when
`φ_3(t) = 0` and `t - 1 ≠ 0`, we get `t·(t + 1) = 0`.

Useful for the FLT case I argument: combined with `p ∤ a` (giving `t ≠ 0`)
and the assumption `φ_3(t) = 0`, we conclude `t = -1`, i.e., `a ≡ b (mod p)`. -/
theorem mirimanoffPolynomial_three_eval_eq_zero_imp (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1)
    (hzero : (mirimanoffPolynomial p 3).eval t = 0) :
    t = 0 ∨ t = -1 := by
  have h := mirimanoffPolynomial_three_eval_mul_X_sub_one_sq p t ht
  rw [hzero, zero_mul] at h
  rcases mul_eq_zero.mp h.symm with h0 | h_plus
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h_plus)

/-- **`φ_3(t) = 0 ↔ t = 0 ∨ t = -1` for `t ≠ 1` and `p ≥ 3` odd.**

Bidirectional version of `mirimanoffPolynomial_three_eval_eq_zero_imp`.
The converse uses:
* For `t = 0`: `φ_3(0) = 0` (constant term vanishes).
* For `t = -1`: `φ_3(-1) = 0` (sum of `k²·(-1)^k` over `k ∈ [1, p-1]`
  vanishes for odd `p`, by `mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd`). -/
theorem mirimanoffPolynomial_three_eval_eq_zero_iff (p : ℕ) [hp : Fact p.Prime]
    (hp_odd : Odd p) (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 3).eval t = 0 ↔ t = 0 ∨ t = -1 := by
  refine ⟨mirimanoffPolynomial_three_eval_eq_zero_imp p t ht, ?_⟩
  rintro (rfl | rfl)
  · -- t = 0 case: φ_3(0) = 0.
    exact mirimanoffPolynomial_eval_zero p 3
  · -- t = -1 case: φ_3(-1) = 0 by mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd.
    exact mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd p hp_odd
      (by norm_num : 1 ≤ 3) (by decide : Odd 3)

/-- **Polynomial identity for `φ_4`.**

In `(ZMod p)[X]`: `φ_4(X) · (X - 1) = -X · φ_2(X) - (2X + 1) · φ_3(X)`.

Derived by differentiating `φ_3 · (X - 1) = -(X + 1) · φ_2` and using
the Euler operator `φ_4 = X · φ_3'`. -/
theorem mirimanoffPolynomial_four_mul_X_sub_one (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p 4 * (Polynomial.X - 1) =
      -Polynomial.X * mirimanoffPolynomial p 2 -
        (2 * Polynomial.X + 1) * mirimanoffPolynomial p 3 := by
  have h3 := mirimanoffPolynomial_three_mul_X_sub_one p
  -- Differentiate φ_3 · (X-1) = -(X+1) · φ_2.
  have h_diff := congrArg Polynomial.derivative h3
  rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_one, sub_zero, mul_one,
      Polynomial.derivative_mul, Polynomial.derivative_neg, Polynomial.derivative_add,
      Polynomial.derivative_X, Polynomial.derivative_one] at h_diff
  -- h_diff : φ_3' · (X-1) + φ_3 = -(1+0) · φ_2 + (-(X+1)) · φ_2'
  -- Use Euler operators.
  have h_euler_4 : mirimanoffPolynomial p 4 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 3) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 3) (by norm_num : 1 ≤ 3)
  have h_euler_3 : mirimanoffPolynomial p 3 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 2) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 2) (by norm_num : 1 ≤ 2)
  linear_combination Polynomial.X * h_diff +
    (Polynomial.X + 1) * h_euler_3 + (Polynomial.X - 1) * h_euler_4

/-- **Closed form for `φ_4(t)` at `t ∈ ZMod p \ {1}`.**

For `t ∈ ZMod p` with `t ≠ 1`, `φ_4(t) · (t - 1)³ = -t · (t² + 4t + 1)`.
Derived from `mirimanoffPolynomial_four_mul_X_sub_one` plus the closed
forms for `φ_2` and `φ_3`. -/
theorem mirimanoffPolynomial_four_eval_mul_X_sub_one_cube (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 4).eval t * (t - 1) ^ 3 =
      -t * (t ^ 2 + 4 * t + 1) := by
  have h := mirimanoffPolynomial_four_mul_X_sub_one p
  have h_eval := congrArg (Polynomial.eval t) h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_ofNat] at h_eval
  -- h_eval : φ_4(t) · (t - 1) = -t · φ_2(t) - (2t + 1) · φ_3(t)
  have h2 := mirimanoffPolynomial_two_eval_mul_one_sub p t ht
  have h3 := mirimanoffPolynomial_three_eval_mul_X_sub_one_sq p t ht
  -- Multiply h_eval by (t - 1)²:
  -- φ_4(t) · (t-1)³ = -t · φ_2(t) · (t-1)² - (2t+1) · φ_3(t) · (t-1)²
  -- Using h2: φ_2(t) · (1-t) = t, so φ_2(t) · (t-1) = -t, hence φ_2(t)·(t-1)² = -t·(t-1).
  -- Using h3: φ_3(t) · (t-1)² = t·(t+1).
  -- So φ_4(t)·(t-1)³ = -t · (-t·(t-1)) - (2t+1) · t·(t+1)
  --                = t²·(t-1) - t·(2t+1)·(t+1)
  --                = t·(t² - t - (2t+1)·(t+1))
  --                = t·(t² - t - 2t² - 3t - 1)
  --                = t·(-t² - 4t - 1)
  --                = -t·(t² + 4t + 1).
  linear_combination (t - 1)^2 * h_eval + t * (t - 1) * h2 - (2 * t + 1) * h3

/-- **Polynomial identity for `φ_5`.**

In `(ZMod p)[X]`: `φ_5(X) · (X - 1) = -X · φ_2(X) - 3X · φ_3(X) - (3X + 1) · φ_4(X)`.

Derived by differentiating `φ_4 · (X - 1) = -X · φ_2 - (2X + 1) · φ_3` and
using Euler operators. -/
theorem mirimanoffPolynomial_five_mul_X_sub_one (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p 5 * (Polynomial.X - 1) =
      -Polynomial.X * mirimanoffPolynomial p 2 -
        3 * Polynomial.X * mirimanoffPolynomial p 3 -
        (3 * Polynomial.X + 1) * mirimanoffPolynomial p 4 := by
  have h4 := mirimanoffPolynomial_four_mul_X_sub_one p
  have h_diff := congrArg Polynomial.derivative h4
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.derivative_add,
    Polynomial.derivative_neg, Polynomial.derivative_ofNat, sub_zero, mul_one,
    zero_mul, zero_add, add_zero] at h_diff
  have h_euler_5 : mirimanoffPolynomial p 5 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 4) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 4) (by norm_num : 1 ≤ 4)
  have h_euler_4 : mirimanoffPolynomial p 4 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 3) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 3) (by norm_num : 1 ≤ 3)
  have h_euler_3 : mirimanoffPolynomial p 3 =
      Polynomial.X * Polynomial.derivative (mirimanoffPolynomial p 2) :=
    mirimanoffPolynomial_succ_eq_X_mul_derivative p (n := 2) (by norm_num : 1 ≤ 2)
  linear_combination Polynomial.X * h_diff +
    Polynomial.X * h_euler_3 + (2 * Polynomial.X + 1) * h_euler_4 +
    (Polynomial.X - 1) * h_euler_5

/-- **Closed form for `φ_5(t)` at `t ∈ ZMod p \ {1}`.**

For `t ∈ ZMod p` with `t ≠ 1`,

  `φ_5(t) · (t - 1)⁴ = t · (t³ + 11t² + 11t + 1)`.

Combines `mirimanoffPolynomial_five_mul_X_sub_one` with closed forms for
`φ_2`, `φ_3`, `φ_4`. -/
theorem mirimanoffPolynomial_five_eval_mul_X_sub_one_pow_four (p : ℕ) [hp : Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 1) :
    (mirimanoffPolynomial p 5).eval t * (t - 1) ^ 4 =
      t * (t ^ 3 + 11 * t ^ 2 + 11 * t + 1) := by
  have h := mirimanoffPolynomial_five_mul_X_sub_one p
  have h_eval := congrArg (Polynomial.eval t) h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_ofNat] at h_eval
  -- h_eval : φ_5(t) · (t - 1) = -t·φ_2(t) - 3t·φ_3(t) - (3t+1)·φ_4(t)
  have h2 := mirimanoffPolynomial_two_eval_mul_one_sub p t ht
  have h3 := mirimanoffPolynomial_three_eval_mul_X_sub_one_sq p t ht
  have h4 := mirimanoffPolynomial_four_eval_mul_X_sub_one_cube p t ht
  linear_combination
    (t - 1)^3 * h_eval + t * (t - 1)^2 * h2 - 3 * t * (t - 1) * h3 - (3 * t + 1) * h4

/-- **Mirimanoff vanishing for odd `n` from `φ_3` vanishing.**

Suppose `t = -a/b ∈ ZMod p` (with `t ≠ 0, 1`) satisfies `φ_3(t) = 0`.
Then `t = -1` (by `mirimanoffPolynomial_three_eval_eq_zero_imp`), and
hence `φ_n(t) = 0` for all odd `n ≥ 1` (by
`mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd`).

This is the *structural reduction* of the Mirimanoff polynomial
vanishing: under `t ≠ 0, 1` (automatic from FLT case I), `φ_3(t) = 0`
is the only nontrivial constraint — the rest of the odd-`n` vanishing
follows automatically. -/
theorem mirimanoffPolynomial_eval_eq_zero_of_phi_3_of_odd
    (p : ℕ) [hp : Fact p.Prime] (hp_odd : Odd p)
    (t : ZMod p) (ht_zero : t ≠ 0) (ht_one : t ≠ 1)
    (h_phi_3 : (mirimanoffPolynomial p 3).eval t = 0)
    {n : ℕ} (hn : 1 ≤ n) (hn_odd : Odd n) :
    (mirimanoffPolynomial p n).eval t = 0 := by
  rcases mirimanoffPolynomial_three_eval_eq_zero_imp p t ht_one h_phi_3 with h0 | h_neg_one
  · exact absurd h0 ht_zero
  · rw [h_neg_one]
    exact mirimanoffPolynomial_eval_neg_one_eq_zero_of_odd p hp_odd hn hn_odd

/-- Every `t : ZMod p` with `t ≠ 1` is a root of `mirimanoffPolynomial p p`. -/
theorem mirimanoffPolynomial_at_p_isRoot (p : ℕ) [Fact p.Prime]
    {t : ZMod p} (ht : t ≠ 1) :
    (mirimanoffPolynomial p p).IsRoot t :=
  mirimanoffPolynomial_at_p_eval_eq_zero_of_ne_one p t ht

/-- **Vanishing of φ_n at 1 for moderate weights.** For `2 ≤ n ≤ p-1`,
`φ_n(1) = 0` in `ZMod p`. This is the standard sum-of-powers identity
`∑_{k=1}^{p-1} k^m = 0` for `1 ≤ m < p-1`. -/
theorem mirimanoffPolynomial_eval_one_eq_zero (p : ℕ) [hp : Fact p.Prime]
    {n : ℕ} (hn_ge : 2 ≤ n) (hn_le : n ≤ p - 1) :
    (mirimanoffPolynomial p n).eval 1 = 0 := by
  classical
  have hp_two : 2 ≤ p := hp.1.two_le
  rw [mirimanoffPolynomial_eval]
  simp only [one_pow, mul_one]
  -- Use bijection Ico 1 p ↔ ZMod p \ {0}
  rw [sum_Ico_natCast_eq_sum_ne_zero (fun x => x ^ (n - 1))]
  -- ∑_{x ∈ ZMod p \ {0}} x^(n-1) = ∑_{x : ZMod p} x^(n-1) - 0^(n-1)
  have hn1_pos : 0 < n - 1 := by omega
  have h_zero_pow : (0 : ZMod p) ^ (n - 1) = 0 := zero_pow hn1_pos.ne'
  have hsum : ∑ x : ZMod p, x ^ (n - 1) =
      ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ (n - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), h_zero_pow, add_zero]
  rw [← hsum]
  -- Apply sum_pow_lt_card_sub_one
  have hp_card : Fintype.card (ZMod p) = p := ZMod.card p
  have h_lt : n - 1 < Fintype.card (ZMod p) - 1 := by rw [hp_card]; omega
  exact FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) (n - 1) h_lt

/-- `φ_p(1) = -1` in `ZMod p`, since `∑_{k=1}^{p-1} 1 = p - 1 = -1`. -/
theorem mirimanoffPolynomial_at_p_eval_one (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).eval 1 = -1 := by
  have hp_pos : 0 < p := hp.1.pos
  rw [mirimanoffPolynomial_at_p, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hp_pos, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- `φ_1(1) = -1` in `ZMod p`. Equivalent to `φ_p(1) = -1` via the
Fermat-shift identity `φ_p = φ_1`. -/
theorem mirimanoffPolynomial_one_eval_one (p : ℕ) [Fact p.Prime] :
    (mirimanoffPolynomial p 1).eval 1 = -1 := by
  rw [← mirimanoffPolynomial_at_p_eq_one]
  exact mirimanoffPolynomial_at_p_eval_one p

/-- Every `t : ZMod p` with `t ≠ 1` is in `roots φ_p`. -/
theorem mirimanoffPolynomial_at_p_mem_roots (p : ℕ) [hp : Fact p.Prime]
    {t : ZMod p} (ht : t ≠ 1) :
    t ∈ (mirimanoffPolynomial p p).roots := by
  rw [Polynomial.mem_roots']
  refine ⟨?_, mirimanoffPolynomial_at_p_isRoot p ht⟩
  intro h
  have h_eval : (mirimanoffPolynomial p p).eval 1 = -1 :=
    mirimanoffPolynomial_at_p_eval_one p
  rw [h, Polynomial.eval_zero] at h_eval
  -- h_eval : 0 = -1 in ZMod p; impossible
  exact one_ne_zero (neg_eq_zero.mp h_eval.symm)

/-- **Biconditional:** `φ_p(t) = 0 ↔ t ≠ 1` in `ZMod p`. -/
theorem mirimanoffPolynomial_at_p_eval_eq_zero_iff (p : ℕ) [Fact p.Prime]
    (t : ZMod p) :
    (mirimanoffPolynomial p p).eval t = 0 ↔ t ≠ 1 := by
  constructor
  · intro h_eval h_eq
    subst h_eq
    have h_one : (mirimanoffPolynomial p p).eval 1 = -1 :=
      mirimanoffPolynomial_at_p_eval_one p
    rw [h_eval] at h_one
    exact one_ne_zero (neg_eq_zero.mp h_one.symm)
  · exact mirimanoffPolynomial_at_p_eval_eq_zero_of_ne_one p t

/-- **Biconditional:** `t` is a root of `φ_p` ↔ `t ≠ 1` in `ZMod p`. -/
theorem mirimanoffPolynomial_at_p_isRoot_iff (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    (mirimanoffPolynomial p p).IsRoot t ↔ t ≠ 1 :=
  mirimanoffPolynomial_at_p_eval_eq_zero_iff p t

/-- **Membership form:** `t ∈ roots φ_p` ↔ `t ≠ 1` in `ZMod p`. -/
theorem mirimanoffPolynomial_at_p_mem_roots_iff (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    t ∈ (mirimanoffPolynomial p p).roots ↔ t ≠ 1 := by
  rw [Polynomial.mem_roots']
  refine ⟨fun h => (mirimanoffPolynomial_at_p_isRoot_iff p t).mp h.2, fun h => ?_⟩
  refine ⟨mirimanoffPolynomial_ne_zero p p, ?_⟩
  exact mirimanoffPolynomial_at_p_isRoot p h

/-- The roots-`Finset` of `φ_p` is exactly `ZMod p \ {1}`. -/
theorem mirimanoffPolynomial_at_p_roots_toFinset (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).roots.toFinset = Finset.univ.erase (1 : ZMod p) := by
  classical
  apply Finset.Subset.antisymm
  · intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots'] at ht
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h_eq
    subst h_eq
    have h_eval : (mirimanoffPolynomial p p).eval 1 = -1 :=
      mirimanoffPolynomial_at_p_eval_one p
    rw [Polynomial.IsRoot.def] at ht
    rw [ht.2] at h_eval
    exact one_ne_zero (neg_eq_zero.mp h_eval.symm)
  · intro t ht
    rw [Finset.mem_erase] at ht
    rw [Multiset.mem_toFinset]
    exact mirimanoffPolynomial_at_p_mem_roots p ht.1

/-- The Multiset of roots of `φ_p` has cardinality exactly `p - 1`. -/
theorem mirimanoffPolynomial_at_p_roots_card (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).roots.card = p - 1 := by
  classical
  have h_natDeg : (mirimanoffPolynomial p p).natDegree = p - 1 :=
    mirimanoffPolynomial_at_p_natDegree p
  have h_le : (mirimanoffPolynomial p p).roots.card ≤
      (mirimanoffPolynomial p p).natDegree :=
    Polynomial.card_roots' _
  rw [h_natDeg] at h_le
  have h_ge : p - 1 ≤ (mirimanoffPolynomial p p).roots.card := by
    have h_finset : (mirimanoffPolynomial p p).roots.toFinset.card =
        (Finset.univ.erase (1 : ZMod p)).card := by
      rw [mirimanoffPolynomial_at_p_roots_toFinset]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card] at h_finset
    calc p - 1 = (mirimanoffPolynomial p p).roots.toFinset.card := h_finset.symm
      _ ≤ (mirimanoffPolynomial p p).roots.card :=
          Multiset.toFinset_card_le _
  omega

/-- The roots of `φ_p` are nodup (each root has multiplicity 1). -/
theorem mirimanoffPolynomial_at_p_roots_nodup (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).roots.Nodup := by
  classical
  rw [← Multiset.toFinset_card_eq_card_iff_nodup,
    mirimanoffPolynomial_at_p_roots_toFinset,
    Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card,
    mirimanoffPolynomial_at_p_roots_card]

/-- **Full factorization of φ_p in (ZMod p)[X]:**
`φ_p = ∏_{a ∈ ZMod p, a ≠ 1} (X - a)`. -/
theorem mirimanoffPolynomial_at_p_eq_prod (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p p =
      ((mirimanoffPolynomial p p).roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
  (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (mirimanoffPolynomial_at_p_monic p)
    (by rw [mirimanoffPolynomial_at_p_roots_card,
        mirimanoffPolynomial_at_p_natDegree])).symm

/-- `φ_p` splits over `ZMod p`: it factors into linear factors. -/
theorem mirimanoffPolynomial_at_p_splits (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).Splits :=
  Polynomial.splits_iff_card_roots.mpr <| by
    rw [mirimanoffPolynomial_at_p_natDegree, mirimanoffPolynomial_at_p_roots_card]

/-- The Multiset of roots of `φ_p` equals the underlying multiset of
the Finset `univ \ {1}`. -/
theorem mirimanoffPolynomial_at_p_roots_eq (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).roots = (Finset.univ.erase (1 : ZMod p)).val := by
  classical
  rw [← mirimanoffPolynomial_at_p_roots_toFinset, Multiset.toFinset_val,
    (mirimanoffPolynomial_at_p_roots_nodup p).dedup]

/-- **Explicit Finset-product factorization of φ_p:**
`φ_p = ∏_{a ∈ ZMod p, a ≠ 1} (X - a)` in `(ZMod p)[X]`. -/
theorem mirimanoffPolynomial_at_p_eq_finset_prod (p : ℕ) [hp : Fact p.Prime] :
    mirimanoffPolynomial p p =
      ∏ a ∈ (Finset.univ.erase (1 : ZMod p)),
        (Polynomial.X - Polynomial.C a) := by
  classical
  rw [mirimanoffPolynomial_at_p_eq_prod, mirimanoffPolynomial_at_p_roots_eq,
    ← Finset.prod_eq_multiset_prod]

/-- For the Finset product over univ.erase 1, the polynomial has natDegree p - 1. -/
theorem mirimanoffPolynomial_at_p_finset_prod_natDegree (p : ℕ) [Fact p.Prime] :
    (∏ a ∈ (Finset.univ.erase (1 : ZMod p)),
      (Polynomial.X - Polynomial.C a)).natDegree = p - 1 := by
  rw [← mirimanoffPolynomial_at_p_eq_finset_prod, mirimanoffPolynomial_natDegree]

/-- **Factorization of X^p - X over ZMod p.**
`X^p - X = ∏_{a ∈ ZMod p} (X - a)` in `(ZMod p)[X]`. -/
theorem X_pow_card_sub_X_eq_prod (p : ℕ) [hp : Fact p.Prime] :
    (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)) =
      ∏ a : ZMod p, (Polynomial.X - Polynomial.C a) := by
  classical
  rw [← mirimanoffPolynomial_at_p_mul_X_sub_one,
    mirimanoffPolynomial_at_p_eq_finset_prod, mul_comm,
    show (Polynomial.X - 1 : Polynomial (ZMod p)) =
        Polynomial.X - Polynomial.C 1 by simp,
    ← Finset.mul_prod_erase Finset.univ
      (fun a : ZMod p => Polynomial.X - Polynomial.C a) (Finset.mem_univ 1)]

/-- The Finset product over univ.erase 1 is monic. -/
theorem mirimanoffPolynomial_at_p_finset_prod_monic (p : ℕ) [Fact p.Prime] :
    (∏ a ∈ (Finset.univ.erase (1 : ZMod p)),
      (Polynomial.X - Polynomial.C a)).Monic := by
  rw [← mirimanoffPolynomial_at_p_eq_finset_prod]
  exact mirimanoffPolynomial_at_p_monic p

/-- `0` is a root of `mirimanoffPolynomial p p`. -/
theorem mirimanoffPolynomial_at_p_zero_isRoot (p : ℕ) [hp : Fact p.Prime] :
    (mirimanoffPolynomial p p).IsRoot 0 := by
  apply mirimanoffPolynomial_at_p_isRoot
  intro h
  exact zero_ne_one h

/-- Iterated Fermat shift: `φ_{n + m·(p-1)} = φ_n` for `n ≥ 1`. -/
theorem mirimanoffPolynomial_add_mul_card_sub_one (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : 1 ≤ n) (m : ℕ) :
    mirimanoffPolynomial p (n + m * (p - 1)) = mirimanoffPolynomial p n := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc,
      mirimanoffPolynomial_add_card_sub_one p (n := n + k * (p - 1)) (by omega), ih]

/-- **Unified φ_n(1) characterization.** For `n ≥ 1`, in `ZMod p`:
`φ_n(1) = -1` if `(p-1) ∣ (n-1)` and `0` otherwise. -/
theorem mirimanoffPolynomial_eval_one (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
    (hn : 1 ≤ n) :
    (mirimanoffPolynomial p n).eval 1 =
      if (p - 1) ∣ (n - 1) then -1 else 0 := by
  have hp_two : 2 ≤ p := hp.1.two_le
  have hpm1_pos : 0 < p - 1 := by omega
  set q := (n - 1) / (p - 1) with hq_def
  set r := (n - 1) % (p - 1) with hr_def
  have hr_lt : r < p - 1 := Nat.mod_lt _ hpm1_pos
  have hn_eq : n - 1 = q * (p - 1) + r := by
    rw [hq_def, hr_def]
    rw [mul_comm, add_comm]
    exact (Nat.mod_add_div (n - 1) (p - 1)).symm
  have hn_decomp : n = (r + 1) + q * (p - 1) := by omega
  have hr1_pos : 1 ≤ r + 1 := by omega
  have hpoly :
      mirimanoffPolynomial p n = mirimanoffPolynomial p (r + 1) := by
    conv_lhs => rw [hn_decomp]
    exact mirimanoffPolynomial_add_mul_card_sub_one p hr1_pos q
  rw [hpoly]
  by_cases hdvd : (p - 1) ∣ (n - 1)
  · rw [if_pos hdvd]
    have hr0 : r = 0 := by
      rw [hr_def, Nat.dvd_iff_mod_eq_zero.mp hdvd]
    rw [hr0, zero_add]
    exact mirimanoffPolynomial_one_eval_one p
  · rw [if_neg hdvd]
    have hr_pos : 1 ≤ r := by
      have hr_ne : r ≠ 0 := fun h => hdvd <| by
        rw [hr_def] at h
        exact Nat.dvd_of_mod_eq_zero h
      omega
    apply mirimanoffPolynomial_eval_one_eq_zero p (n := r + 1) (by omega) (by omega)

/-- For `n ≥ 1` with `(p-1) ∤ (n-1)`, evaluating at `1 ∈ R` for any
`(ZMod p)`-algebra `R` gives `0`. -/
theorem mirimanoffPolynomial_aeval_one_eq_zero (p : ℕ) [Fact p.Prime]
    {n : ℕ} (hn : 1 ≤ n) (h_dvd : ¬ (p - 1) ∣ (n - 1))
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] :
    (mirimanoffPolynomial p n).aeval (1 : R) = 0 := by
  have h := mirimanoffPolynomial_eval_one p hn
  rw [if_neg h_dvd] at h
  have hone : (1 : R) = algebraMap (ZMod p) R 1 := (map_one _).symm
  rw [hone, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, h, map_zero]

/-- For `n ≥ 1` with `(p-1) ∣ (n-1)`, evaluating at `1 ∈ R` for any
`(ZMod p)`-algebra `R` gives `-1`. -/
theorem mirimanoffPolynomial_aeval_one_eq_neg_one (p : ℕ) [Fact p.Prime]
    {n : ℕ} (hn : 1 ≤ n) (h_dvd : (p - 1) ∣ (n - 1))
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] :
    (mirimanoffPolynomial p n).aeval (1 : R) = -1 := by
  have h := mirimanoffPolynomial_eval_one p hn
  rw [if_pos h_dvd] at h
  have hone : (1 : R) = algebraMap (ZMod p) R 1 := (map_one _).symm
  rw [hone, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, h, map_neg, map_one]

/-- The aeval form of `φ_p(1) = -1`: in any `(ZMod p)`-algebra `R`,
`φ_p.aeval (1 : R) = -1`. -/
theorem mirimanoffPolynomial_aeval_at_p_one_eq_neg_one (p : ℕ) [Fact p.Prime]
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] :
    (mirimanoffPolynomial p p).aeval (1 : R) = -1 := by
  have hone : (1 : R) = algebraMap (ZMod p) R 1 := (map_one _).symm
  rw [hone, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    mirimanoffPolynomial_at_p_eval_one, map_neg, map_one]

/-- Evaluating any Mirimanoff polynomial at `0 ∈ R` for any
`(ZMod p)`-algebra `R` gives `0`. -/
theorem mirimanoffPolynomial_aeval_zero (p : ℕ) [Fact p.Prime] (n : ℕ)
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] :
    (mirimanoffPolynomial p n).aeval (0 : R) = 0 := by
  have h := mirimanoffPolynomial_eval_zero p n
  have hzero : (0 : R) = algebraMap (ZMod p) R 0 := (map_zero _).symm
  rw [hzero, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, h, map_zero]

/-- The aeval form of `φ_p(0) = 0`: in any `(ZMod p)`-algebra `R`,
`φ_p.aeval (0 : R) = 0`. -/
theorem mirimanoffPolynomial_aeval_at_p_zero_eq_zero (p : ℕ) [Fact p.Prime]
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] :
    (mirimanoffPolynomial p p).aeval (0 : R) = 0 :=
  mirimanoffPolynomial_aeval_zero p p R

/-- The aeval form of `φ_p(-1) = 0` for odd `p`: in any `(ZMod p)`-algebra
`R`, `φ_p.aeval (-1 : R) = 0`. -/
theorem mirimanoffPolynomial_aeval_at_p_neg_one_eq_zero (p : ℕ) [hp : Fact p.Prime]
    (hp_odd : Odd p) (R : Type*) [CommRing R] [Algebra (ZMod p) R] :
    (mirimanoffPolynomial p p).aeval (-1 : R) = 0 :=
  mirimanoffPolynomial_aeval_neg_one_eq_zero_of_odd p hp_odd hp.1.pos hp_odd R

/-- Cast form: in any `(ZMod p)`-algebra `R`, `φ_n.aeval (algebraMap (ZMod p) R c) =
algebraMap (ZMod p) R (φ_n.eval c)`. -/
theorem mirimanoffPolynomial_aeval_algebraMap (p : ℕ) [Fact p.Prime] (n : ℕ)
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] (c : ZMod p) :
    (mirimanoffPolynomial p n).aeval (algebraMap (ZMod p) R c) =
      algebraMap (ZMod p) R ((mirimanoffPolynomial p n).eval c) :=
  Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval c (mirimanoffPolynomial p n)

/-- **Generalized Frobenius vanishing.** In any integral domain `R` that
is a `(ZMod p)`-algebra: if `t : R` satisfies `t^p = t` (Frobenius
fixed point) and `t ≠ 1`, then `φ_p.aeval t = 0`. -/
theorem mirimanoffPolynomial_at_p_aeval_eq_zero_of_frobenius_fixed
    (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R]
    [Algebra (ZMod p) R] {t : R} (ht_frob : t ^ p = t) (ht_ne : t ≠ 1) :
    (mirimanoffPolynomial p p).aeval t = 0 := by
  have h_telescope := mirimanoffPolynomial_at_p_aeval_mul p R t
  rw [ht_frob, sub_self] at h_telescope
  exact (mul_eq_zero.mp h_telescope).resolve_right (sub_ne_zero.mpr ht_ne)

/-- **Strengthened biconditional in domains with t^p = t.** For an
integral-domain (ZMod p)-algebra and a Frobenius-fixed t (i.e. t^p = t),
φ_p.aeval t = 0 iff t ≠ 1. -/
theorem mirimanoffPolynomial_at_p_aeval_eq_zero_iff_of_frobenius_fixed
    (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R]
    [Algebra (ZMod p) R] {t : R} (ht_frob : t ^ p = t) :
    (mirimanoffPolynomial p p).aeval t = 0 ↔ t ≠ 1 := by
  refine ⟨fun h_eval h_eq => ?_,
    mirimanoffPolynomial_at_p_aeval_eq_zero_of_frobenius_fixed p R ht_frob⟩
  subst h_eq
  -- aeval at 1 evaluates to algebraMap of φ_p.eval 1 = -1
  rw [show (1 : R) = algebraMap (ZMod p) R 1 from (map_one _).symm,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    mirimanoffPolynomial_at_p_eval_one] at h_eval
  -- h_eval : algebraMap (ZMod p) R (-1) = 0
  rw [map_neg, map_one, neg_eq_zero] at h_eval
  exact (one_ne_zero h_eval)

end MirimanoffPolynomial
end FLT37

end BernoulliRegular

end

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import PadicLFunctions.KubotaLeopoldt.ZetaValues

/-!
# Generalised Bernoulli numbers (the L-values of RJW §5)

RJW route the special values `L(χ, −k)` through the complex Mellin theory
(Lem 5.5/5.9 via `thm:l-function`, §2). As in §4 (where `ζ(1−k)` was the
rational `zetaNeg` and the complex comparison was quarantined), the `p`-adic
statements use the *generalised Bernoulli numbers* `B_{k,χ}` as the canonical
value, following the cross-reference Washington, *Introduction to Cyclotomic
Fields* §4.1–4.2 ("B_{n,χ}" and Thm 4.2: `L(1−n, χ) = −B_{n,χ}/n`); the
complex bridge is `GenBernoulliComplex.lean`.

`B_{k,χ} := N^{k−1} ∑_{a=1}^{N} χ(a)·B_k(a/N)` for `χ` mod `N` (Washington
Prop 4.1's polynomial form; the `a`-range `1..N` matters — it makes the
trivial-character case reduce to `B_k(1) = bernoulli' k`).
-/

open Finset

namespace PadicLFunctions

variable {L : Type*} [Field L] [CharZero L] {N : ℕ} [NeZero N]

/-- L5.1.9: the generalised Bernoulli number `B_{k,χ} ∈ L` of a Dirichlet
character `χ` mod `N` valued in a characteristic-zero field:
`B_{k,χ} = N^{k−1} ∑_{a=1}^{N} χ(a)·B_k(a/N)`
(Bernoulli-polynomial form; Washington §4.1, Prop 4.1). -/
noncomputable def _root_.DirichletCharacter.genBernoulli
    (χ : DirichletCharacter L N) (k : ℕ) : L :=
  (N : L) ^ ((k : ℤ) - 1) *
    ∑ a ∈ range N, χ (a + 1 : ℕ) *
      Polynomial.eval (((a : L) + 1) / (N : L)) ((Polynomial.bernoulli k).map (algebraMap ℚ L))

/-- The L-value `L(χ, −k)` in its `p`-adic incarnation:
`LvalNeg χ k = −B_{k+1,χ}/(k+1)` (Washington Thm 4.2). -/
noncomputable def LvalNeg (χ : DirichletCharacter L N) (k : ℕ) : L :=
  -(χ.genBernoulli (k + 1)) / (k + 1)

/-- At the trivial character mod 1, the generalised Bernoulli numbers are the
`bernoulli'` numbers (`B_k(1) = bernoulli' k`), so `LvalNeg` matches §4's
`zetaNeg`-route values: `ζ(−k) = −B'_{k+1}/(k+1)`. -/
theorem genBernoulli_one (k : ℕ) :
    (1 : DirichletCharacter L 1).genBernoulli k = (bernoulli' k : ℚ) • (1 : L) := by
  simp only [DirichletCharacter.genBernoulli, Finset.range_one, Finset.sum_singleton,
    Nat.cast_one, one_zpow, one_mul, Nat.cast_zero, zero_add, div_one, map_one]
  rw [Polynomial.eval_one_map, Polynomial.bernoulli_eval_one, Algebra.smul_def, mul_one]

/-- For `N > 1`, the defining `1..N` range sum of `genBernoulli` equals the
`ZMod N`-indexed sum (shift `a ↦ a + 1`; at the boundary `a + 1 = N` both
terms vanish through `χ(0) = 0`):
`B_{k,χ} = N^{k−1} ∑_{b : ZMod N} χ(b)·B_k(b.val/N)`. -/
theorem genBernoulli_eq_zmod_sum [Fact (1 < N)] (χ : DirichletCharacter L N) (k : ℕ) :
    χ.genBernoulli k = (N : L) ^ ((k : ℤ) - 1) *
      ∑ b : ZMod N, χ b *
        Polynomial.eval (((b.val : ℕ) : L) / (N : L))
          ((Polynomial.bernoulli k).map (algebraMap ℚ L)) := by
  have hN2 : 1 < N := Fact.out
  have hχ0 : χ (0 : ZMod N) = 0 := χ.map_nonunit not_isUnit_zero
  rw [DirichletCharacter.genBernoulli]
  congr 1
  have hinj : Set.InjOn (fun a : ℕ => ((a + 1 : ℕ) : ZMod N)) (range N) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hmod := (ZMod.natCast_eq_natCast_iff' (a+1) (b+1) N).1 hab
    rcases eq_or_ne (a+1) N with h1 | h1 <;> rcases eq_or_ne (b+1) N with h2 | h2
    · omega
    · rw [h1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
    · rw [h2, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
  rw [show (Finset.univ : Finset (ZMod N))
      = Finset.image (fun a : ℕ => ((a + 1 : ℕ) : ZMod N)) (range N) from by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rcases eq_or_ne (a + 1) N with hend | hend
  · -- boundary `a+1 = N`: both sides vanish through `χ(0) = 0`
    have hcast : ((a + 1 : ℕ) : ZMod N) = 0 := by rw [hend, ZMod.natCast_self]
    simp [hcast, hχ0]
  · have hval : ((a + 1 : ℕ) : ZMod N).val = a + 1 :=
      ZMod.val_natCast_of_lt (by omega)
    rw [hval]
    push_cast
    ring_nf

/-- L5.1.11 (parity vanishing): `B_{k,χ} = 0` when `χ(−1) ≠ (−1)^k` —
except in the degenerate trivial-character case `k = 1`.

Source (TeX 1744–1746): "we recover the well-known fact that `L(χ,−k) = 0`
if `χ(−1)(−1)^k = 1`" (shifted by one index here). Route: the involution
`a ↦ N − a` on the defining sum plus `B_k(1−x) = (−1)^k B_k(x)`. -/
theorem genBernoulli_eq_zero (χ : DirichletCharacter L N) {k : ℕ}
    (h : χ (-1) ≠ (-1 : L) ^ k) (hk : χ ≠ 1 ∨ k ≠ 1) :
    χ.genBernoulli k = 0 := by
  set f : ℚ →+* L := algebraMap ℚ L with hf
  set B : Polynomial L := (Polynomial.bernoulli k).map f with hB
  -- the reflection identity, mapped through the algebra map
  have hrefl : ∀ x : ℚ, B.eval (f (1 - x)) = (-1 : L) ^ k * B.eval (f x) := by
    intro x
    rw [hB, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, Polynomial.bernoulli_eval_one_sub, map_mul, map_pow,
      map_neg, map_one]
  rcases eq_or_ne N 1 with rfl | hN
  · -- level one: `χ = 1`, so `k` is odd and `≠ 1`, and `B'_k = 0`
    have hχ1 : χ = 1 := DirichletCharacter.level_one χ
    have hodd : Odd k := by
      by_contra he
      rw [Nat.not_odd_iff_even] at he
      refine h ?_
      rw [hχ1, he.neg_one_pow]
      exact MulChar.one_apply (isUnit_one.neg)
    have hk1 : k ≠ 1 := hk.resolve_left (· hχ1)
    rw [hχ1, genBernoulli_one, bernoulli'_eq_zero_of_odd hodd (by
      rcases hodd with ⟨m, hm⟩
      omega)]
    simp
  -- main case `N ≥ 2`
  have hN2 : 2 ≤ N := by
    have := NeZero.pos N
    omega
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hχ0 : χ (0 : ZMod N) = 0 := χ.map_nonunit not_isUnit_zero
  have hNL : ((N : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- the `ZMod`-indexed sum
  set T : L := ∑ b : ZMod N, χ b * B.eval (((b.val : ℕ) : L) / (N : L)) with hT
  -- reflection: `T = χ(−1)·(−1)^k · T` via the negation bijection on `ZMod N`
  have hflip : T = (χ (-1) * (-1 : L) ^ k) * T := by
    rw [hT, Finset.mul_sum, ← Equiv.sum_comp (Equiv.neg (ZMod N))
      (fun b => χ b * B.eval (((b.val : ℕ) : L) / (N : L)))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne b 0 with rfl | hb0
    · simp only [Equiv.neg_apply, neg_zero, hχ0, zero_mul, mul_zero]
    · rw [Equiv.neg_apply]
      have hχneg : χ (-b) = χ (-1) * χ b := by
        rw [show (-b : ZMod N) = -1 * b from by ring, map_mul]
      haveI : NeZero b := ⟨hb0⟩
      have hvneg : ((-b).val : ℕ) = N - b.val := ZMod.val_neg_of_ne_zero b
      have hble : b.val ≤ N := (ZMod.val_lt b).le
      have hpt : (((-b).val : ℕ) : L) / (N : L) = f (1 - (b.val : ℚ) / (N : ℚ)) := by
        rw [hvneg, map_sub, map_one, map_div₀, map_natCast, map_natCast,
          Nat.cast_sub hble]
        field_simp
      have hpt2 : ((b.val : ℕ) : L) / (N : L) = f ((b.val : ℚ) / (N : ℚ)) := by
        rw [map_div₀, map_natCast, map_natCast]
      rw [hpt, hrefl, hχneg, hpt2]
      ring
  -- conclude: the factor `1 − χ(−1)(−1)^k = 2 ≠ 0`
  have hu2 : χ (-1) * χ (-1) = 1 := by simp [← map_mul]
  have hkey : χ (-1) * (-1 : L) ^ k = -1 := by
    rcases mul_self_eq_one_iff.1 hu2 with h1 | h1 <;>
      rcases neg_one_pow_eq_or L k with h2 | h2 <;>
      rw [h1, h2] <;> rw [h1, h2] at h <;> first | exact absurd rfl h | ring
  rw [hkey] at hflip
  have hT0 : T = 0 :=
    (mul_eq_zero.1 (by linear_combination hflip : (2 : L) * T = 0)).resolve_left two_ne_zero
  rw [genBernoulli_eq_zmod_sum χ k, ← hT, hT0, mul_zero]

section generatingFunction

open PowerSeries

/-- L5.1.10a: the generating-function characterisation of `B_{k,χ}` (cleared
form): `(∑_k B_{k,χ} t^k/k!) · (e^{Nt} − 1) = ∑_{a=1}^{N} χ(a)·t·e^{at}`,
an identity in `L⟦t⟧` (Washington §4.1's defining identity, equivalent to the
polynomial definition above by the Bernoulli-polynomial generating function).
This is the §5 analogue of mathlib's `bernoulliPowerSeries_mul_exp_sub_one`
and drives the moment computations (T030–T033 pattern). -/
theorem genBernoulliPowerSeries_mul (χ : DirichletCharacter L N) :
    (PowerSeries.mk fun k => χ.genBernoulli k * (k.factorial : L)⁻¹) *
        (rescale (N : L) (exp L) - 1)
      = ∑ a ∈ range N, χ (a + 1 : ℕ) • (X * rescale ((a : L) + 1) (exp L)) := by
  have hN : (N : L) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hCN : (C (N : L)) ≠ 0 := fun h =>
    hN (by simpa using congrArg (constantCoeff) h)
  refine mul_left_cancel₀ hCN ?_
  -- the per-`a` identity: mathlib's Bernoulli generating function at
  -- `t = (a+1)/N`, rescaled by `N`
  have hper : ∀ a : ℕ,
      rescale (N : L) (PowerSeries.mk fun n =>
          Polynomial.aeval (((a : L) + 1) / (N : L))
            ((1 / n.factorial : ℚ) • Polynomial.bernoulli n))
        * (rescale (N : L) (exp L) - 1)
      = C (N : L) * (X * rescale ((a : L) + 1) (exp L)) := by
    intro a
    have h := congrArg (rescale (N : L))
      (Polynomial.bernoulli_generating_function (((a : L) + 1) / (N : L)))
    rwa [map_mul, map_sub, map_one, map_mul, rescale_rescale, rescale_X,
      div_mul_cancel₀ _ hN, mul_assoc] at h
  -- the χ-weighted sum of the rescaled generating functions is `C N · LHS`
  have hkey : C (N : L) *
        (PowerSeries.mk fun k => χ.genBernoulli k * (k.factorial : L)⁻¹)
      = ∑ a ∈ range N, χ (a + 1 : ℕ) •
          rescale (N : L) (PowerSeries.mk fun n =>
            Polynomial.aeval (((a : L) + 1) / (N : L))
              ((1 / n.factorial : ℚ) • Polynomial.bernoulli n)) := by
    ext k
    rw [coeff_C_mul, coeff_mk, map_sum]
    simp only [coeff_smul, coeff_rescale, coeff_mk, smul_eq_mul]
    have hzp : ((N : L)) ^ (k : ℕ) = (N : L) * (N : L) ^ ((k : ℤ) - 1) := by
      rw [zpow_sub_one₀ hN, ← zpow_natCast (N : L) k]
      field_simp
    rw [DirichletCharacter.genBernoulli]
    simp only [hzp, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Algebra.smul_def, map_div₀, map_one,
      map_natCast (algebraMap ℚ L) k.factorial,
      Polynomial.aeval_def, ← Polynomial.eval_map, one_div]
    ring
  calc C (N : L) * ((PowerSeries.mk fun k => χ.genBernoulli k * (k.factorial : L)⁻¹)
        * (rescale (N : L) (exp L) - 1))
      = (C (N : L) * PowerSeries.mk fun k => χ.genBernoulli k * (k.factorial : L)⁻¹)
          * (rescale (N : L) (exp L) - 1) := (mul_assoc _ _ _).symm
    _ = (∑ a ∈ range N, χ (a + 1 : ℕ) •
          rescale (N : L) (PowerSeries.mk fun n =>
            Polynomial.aeval (((a : L) + 1) / (N : L))
              ((1 / n.factorial : ℚ) • Polynomial.bernoulli n)))
          * (rescale (N : L) (exp L) - 1) := by rw [hkey]
    _ = ∑ a ∈ range N, χ (a + 1 : ℕ) •
          (rescale (N : L) (PowerSeries.mk fun n =>
            Polynomial.aeval (((a : L) + 1) / (N : L))
              ((1 / n.factorial : ℚ) • Polynomial.bernoulli n))
            * (rescale (N : L) (exp L) - 1)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _
    _ = ∑ a ∈ range N, χ (a + 1 : ℕ) •
          (C (N : L) * (X * rescale ((a : L) + 1) (exp L))) :=
        Finset.sum_congr rfl fun a _ => by rw [hper a]
    _ = C (N : L) * ∑ a ∈ range N, χ (a + 1 : ℕ) •
          (X * rescale ((a : L) + 1) (exp L)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => (mul_smul_comm _ _ _).symm

/-- L5.1.10c: the cyclotomic product `∏_{c<M} (ζ^c·Y − 1) = Y^M − 1` for `ζ` a
primitive `M`-th root of unity and **odd** `M` (used to clear the denominators
of `F_{χ,a}` at `Y = 1+X`, at `M = p^n` with `p` odd). The skeleton's
unconditional form was FALSE for even `M` (at `M = 2`, `ζ = −1`:
`(Y−1)(−Y−1) = 1−Y²`) — statement corrected at proof time, recorded in T503. -/
theorem prod_primitiveRoot_mul_sub_one {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {M : ℕ} (hM : Odd M) (hζ : IsPrimitiveRoot ζ M) (Y : R) :
    ∏ c ∈ range M, (ζ ^ c * Y - 1) = Y ^ M - 1 := by
  have hM0 : 0 < M := hM.pos
  have hpoly := X_pow_sub_C_eq_prod hζ hM0 (rfl : Y ^ M = Y ^ M)
  have heval := congrArg (Polynomial.eval 1) hpoly
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, one_pow] at heval
  rw [show (∏ c ∈ range M, (ζ ^ c * Y - 1)) = ∏ c ∈ range M, -(1 - ζ ^ c * Y) from
      Finset.prod_congr rfl fun c _ => (neg_sub _ _).symm,
    Finset.prod_neg, ← heval, Finset.card_range, hM.neg_one_pow]
  ring

end generatingFunction

end PadicLFunctions

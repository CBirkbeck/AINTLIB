module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic

/-!
# Arithmetic bounds for finite logarithm denominators

This file records the elementary natural-number estimates used to control the
`Q`-adic orders of terms `x^n / n` in the finite-logarithm argument.  The
valuation `v_ell(n)` is written as `n.factorization ell`.
-/

@[expose] public section

namespace Nat

/-- Bernoulli's inequality in the natural-number form needed for valuation
bounds. -/
theorem mul_pred_le_pow_sub_one (a n : ℕ) (ha : 1 ≤ a) :
    n * (a - 1) ≤ a ^ n - 1 := by
  have ha_pos : 0 < a := Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  have hpow_one : 1 ≤ a ^ n := Nat.one_le_pow n a ha_pos
  have hbern :
      (1 : ℤ) + (n : ℤ) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ n :=
    one_add_mul_sub_le_pow (by omega) n
  have hcast :
      ((n * (a - 1) : ℕ) : ℤ) ≤ ((a ^ n - 1 : ℕ) : ℤ) := by
    have hpow_cast : ((a ^ n : ℕ) : ℤ) = (a : ℤ) ^ n :=
      Nat.cast_pow a n
    rw [Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub hpow_one, hpow_cast,
      Nat.cast_one]
    change (n : ℤ) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ n - 1
    omega
  exact_mod_cast hcast

/-- For nonzero `n`, `(ell - 1) * v_ell(n)` is at most `n - 1`. -/
theorem factorization_mul_pred_le_pred {ell n : ℕ}
    (hell : ell.Prime) (hn : n ≠ 0) :
    n.factorization ell * (ell - 1) ≤ n - 1 := by
  let f : ℕ := n.factorization ell
  have hdvd : ell ^ f ∣ n :=
    (hell.pow_dvd_iff_le_factorization hn).2 le_rfl
  have hpow_le : ell ^ f ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hmul_le : f * (ell - 1) ≤ ell ^ f - 1 :=
    Nat.mul_pred_le_pow_sub_one ell f hell.pos
  exact hmul_le.trans (Nat.sub_le_sub_right hpow_le 1)

/-- Ticket-form version: `n - (ell - 1) * v_ell(n) >= 1` for nonzero `n`. -/
theorem one_le_sub_pred_mul_factorization {ell n : ℕ}
    (hell : ell.Prime) (hn : n ≠ 0) :
    1 ≤ n - (ell - 1) * n.factorization ell := by
  have h := Nat.factorization_mul_pred_le_pred (ell := ell) (n := n) hell hn
  rw [Nat.mul_comm] at h
  omega

/-- A sharper denominator estimate: after removing `(ell - 1) * v_ell(n)`,
at least `n / ell` remains. -/
theorem pred_mul_factorization_add_div_le {ell n : ℕ}
    (hell : ell.Prime) :
    (ell - 1) * n.factorization ell + n / ell ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  let v : ℕ := n.factorization ell
  let c : ℕ := ordCompl[ell] n
  have hc_pos : 0 < c := by
    simpa [c] using ordCompl_pos ell hn
  have hn_eq : ell ^ v * c = n := by
    simpa [v, c] using ordProj_mul_ordCompl_eq_self n ell
  by_cases hv : v = 0
  · simp [v, hv, Nat.div_le_self]
  obtain ⟨t, ht⟩ : ∃ t, v = t + 1 := Nat.exists_eq_succ_of_ne_zero hv
  have hpow_split : ell ^ v = ell * ell ^ (v - 1) := by
    rw [ht]
    simp [pow_succ, Nat.mul_comm]
  have hv_le_pow : v ≤ ell ^ (v - 1) := by
    rw [ht]
    simpa using Nat.succ_le_of_lt (Nat.lt_pow_self (n := t) hell.one_lt)
  have hv_le : v ≤ ell ^ (v - 1) * c :=
    hv_le_pow.trans (Nat.le_mul_of_pos_right _ hc_pos)
  have hmul_le :
      (ell - 1) * v ≤ (ell - 1) * (ell ^ (v - 1) * c) :=
    Nat.mul_le_mul_left _ hv_le
  have hdiv :
      n / ell = ell ^ (v - 1) * c := by
    calc
      n / ell = (ell ^ v * c) / ell := by rw [hn_eq]
      _ = ((ell * ell ^ (v - 1)) * c) / ell := by rw [hpow_split]
      _ = (ell * (ell ^ (v - 1) * c)) / ell := by rw [Nat.mul_assoc]
      _ = ell ^ (v - 1) * c := by
        rw [Nat.mul_comm ell, Nat.mul_div_left _ hell.pos]
  calc
    (ell - 1) * n.factorization ell + n / ell
        = (ell - 1) * v + ell ^ (v - 1) * c := by rw [hdiv]
    _ ≤ (ell - 1) * (ell ^ (v - 1) * c) + ell ^ (v - 1) * c :=
        Nat.add_le_add_right hmul_le _
    _ = ((ell - 1) + 1) * (ell ^ (v - 1) * c) := by
        rw [Nat.add_mul, one_mul]
    _ = ell * (ell ^ (v - 1) * c) := by rw [Nat.sub_add_cancel hell.pos]
    _ = ell ^ v * c := by rw [hpow_split, Nat.mul_assoc]
    _ = n := hn_eq

/-- Ticket-form tail bound:
`n >= ell * (N+1) -> n - (ell - 1) * v_ell(n) >= N+1`. -/
theorem succ_le_sub_pred_mul_factorization_of_mul_succ_le {ell N n : ℕ}
    (hell : ell.Prime) (hn : ell * (N + 1) ≤ n) :
    N + 1 ≤ n - (ell - 1) * n.factorization ell := by
  have hdiv : N + 1 ≤ n / ell := by
    rw [Nat.le_div_iff_mul_le hell.pos]
    simpa [Nat.mul_comm] using hn
  have hden := Nat.pred_mul_factorization_add_div_le (ell := ell) (n := n) hell
  omega

/-- If `n <= d`, then replacing `d` by the smaller denominator index `n`
costs at most `d - n` after division by `ell`. -/
theorem div_le_div_add_sub {ell n d : ℕ} (hell : 0 < ell) (hnd : n ≤ d) :
    d / ell ≤ n / ell + (d - n) := by
  rw [Nat.div_le_iff_le_mul_add_pred hell]
  have hmod_le : n % ell ≤ ell - 1 := by
    simpa using Nat.le_pred_of_lt (Nat.mod_lt n hell)
  have hn_bound : n ≤ ell * (n / ell) + (ell - 1) := by
    calc
      n = ell * (n / ell) + n % ell := (Nat.div_add_mod n ell).symm
      _ ≤ ell * (n / ell) + (ell - 1) := Nat.add_le_add_left hmod_le _
  have hsub_le : d - n ≤ ell * (d - n) := by
    have hell_one : 1 ≤ ell := hell
    simpa using Nat.mul_le_mul_right (d - n) hell_one
  calc
    d = n + (d - n) := (Nat.add_sub_of_le hnd).symm
    _ ≤ (ell * (n / ell) + (ell - 1)) + (d - n) :=
        Nat.add_le_add_right hn_bound _
    _ ≤ (ell * (n / ell) + (ell - 1)) + ell * (d - n) :=
        Nat.add_le_add_left hsub_le _
    _ = ell * (n / ell + (d - n)) + (ell - 1) := by
        rw [Nat.mul_add]
        omega

/-- Total-degree tail bound for logarithm terms: if a homogeneous piece has
total degree at least `ell * (N+1)` and comes from the `n`-th logarithm term
with `n <= d`, then its `Q`-order is still at least `N+1` after cancelling the
`ell`-power part of the denominator. -/
theorem succ_le_sub_factorization_mul_pred_of_mul_succ_le_of_le {ell N n d : ℕ}
    (hell : ell.Prime) (hd : ell * (N + 1) ≤ d) (hnd : n ≤ d) :
    N + 1 ≤ d - n.factorization ell * (ell - 1) := by
  have hell_pos : 0 < ell := hell.pos
  have hdiv : N + 1 ≤ d / ell := by
    rw [Nat.le_div_iff_mul_le hell_pos]
    simpa [Nat.mul_comm] using hd
  have hddiv : d / ell ≤ n / ell + (d - n) :=
    Nat.div_le_div_add_sub hell_pos hnd
  have hN : N + 1 ≤ n / ell + (d - n) := hdiv.trans hddiv
  have hden :
      n.factorization ell * (ell - 1) + n / ell ≤ n := by
    simpa [Nat.mul_comm] using
      Nat.pred_mul_factorization_add_div_le (ell := ell) (n := n) hell
  have htotal : n.factorization ell * (ell - 1) + (N + 1) ≤ d := by
    calc
      n.factorization ell * (ell - 1) + (N + 1)
          ≤ n.factorization ell * (ell - 1) + (n / ell + (d - n)) :=
            Nat.add_le_add_left hN _
      _ = (n.factorization ell * (ell - 1) + n / ell) + (d - n) := by
            omega
      _ ≤ n + (d - n) := Nat.add_le_add_right hden _
      _ = d := Nat.add_sub_of_le hnd
  have htotal' : N + 1 + n.factorization ell * (ell - 1) ≤ d := by
    omega
  exact Nat.le_sub_of_add_le htotal'

/-- If `2 <= s` and `2 <= n`, then the nonlinear log terms have strictly
higher order than `s` after dividing by `n`. -/
theorem lt_mul_sub_pred_mul_factorization {ell n s : ℕ}
    (hell : ell.Prime) (hs : 2 ≤ s) (hn : 2 ≤ n) :
    s < n * s - (ell - 1) * n.factorization ell := by
  have hn0 : n ≠ 0 := by omega
  have hfac := Nat.factorization_mul_pred_le_pred (ell := ell) (n := n) hell hn0
  rw [Nat.mul_comm] at hfac
  have hs_pred : 1 ≤ s - 1 := by omega
  have hs_le_two_mul : s ≤ 2 * (s - 1) := by omega
  have hs_le_n_mul : s ≤ n * (s - 1) :=
    hs_le_two_mul.trans (Nat.mul_le_mul_right (s - 1) hn)
  have hns : n + s ≤ n * s := by
    calc
      n + s ≤ n + n * (s - 1) := Nat.add_le_add_left hs_le_n_mul n
      _ = n * s := by
        rw [Nat.add_comm, ← Nat.mul_succ, Nat.succ_eq_add_one,
          Nat.sub_add_cancel (by omega : 1 ≤ s)]
  have hsum : (ell - 1) * n.factorization ell + (s + 1) ≤ n * s := by
    calc
      (ell - 1) * n.factorization ell + (s + 1)
          ≤ (n - 1) + (s + 1) := Nat.add_le_add_right hfac _
      _ = n + s := by omega
      _ ≤ n * s := hns
  omega

/-- Non-strict equivalent of `Nat.lt_mul_sub_pred_mul_factorization`. -/
theorem succ_le_mul_sub_pred_mul_factorization {ell n s : ℕ}
    (hell : ell.Prime) (hs : 2 ≤ s) (hn : 2 ≤ n) :
    s + 1 ≤ n * s - (ell - 1) * n.factorization ell :=
  Nat.succ_le_iff.2 (Nat.lt_mul_sub_pred_mul_factorization hell hs hn)

end Nat

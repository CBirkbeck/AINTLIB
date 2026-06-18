/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, David Kurniadi Angdinata
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic.IntervalCases

/-!
# Additional lemmas for elliptic divisibility sequences

This file provides definitions and lemmas about normalised elliptic divisibility sequences
that are not yet in mathlib. These are needed for the division polynomial / ZSMul development.

The key results are:
* `IsEllSequence.normEDS`: a normalised EDS is an elliptic sequence.
* `IsEllSequence.ext`: two elliptic sequences with the same first four terms are equal.
* `normEDS_two_three_two`: when `b = 2, c = 3, d = 2`, the normalised EDS is the identity.
* `complEDSAux₂`: auxiliary complement used in the `ω` definition.
* `redInvarDenom`, `redInvarNum`: reduced invariant decomposition.

Ported from the LutzNagell project (`LutzNagell/EllipticDivisibilitySequence.lean`).
-/

open scoped nonZeroDivisors

namespace EllSequence

variable {R : Type*} [CommRing R] (W : ℤ → R)

/-- The expression `W((m+n)/2) * W((m-n)/2)` is the basic building block of elliptic relations,
where integers `m` and `n` should have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)

/-- The four-index elliptic relation, defined in terms of `addMulSub`,
featuring the three partitions of four indices into two pairs.
Intended to apply to four integers of the same parity. -/
def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c

/-- The defining property of Stange's elliptic nets,
equivalent to a suitable valid (same-parity indices) `rel₄` relation. -/
def net (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r
    - W (p + r + s) * W (p - r) * W (q + s) * W q
    + W (q + r + s) * W (q - r) * W (p + s) * W p

variable {W} in
lemma net_eq_rel₄ {p q r s : ℤ} :
    net W p q r s = rel₄ W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [net, rel₄, addMulSub, add_add_add_comm _ s, add_sub_add_comm, sub_self, add_zero,
    add_assoc, ← two_mul, add_sub_cancel_right, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]
  ring

lemma net_add_sub_iff (m n : ℤ) :
    net W (m + n) m (m - n) n = 0 ↔
      W (2 * (m + n)) * W (m - n) * W m * W n =
        (W (2 * m + n) * W (2 * n) * W m - W (m + 2 * n) * W (2 * m) * W n) * W (m + n) := by
  simp_rw [net, show m + n + m + n = 2 * (m + n) by ring,
    show m + n - m = n by ring, show m - n + n = m by ring,
    show m + n + (m - n) + n = 2 * m + n by ring,
    show m + n - (m - n) = 2 * n by ring,
    show m + (m - n) + n = 2 * m by ring,
    show m - (m - n) = n by ring, show m + n + n = m + 2 * n by ring]
  constructor <;> intro h <;> linear_combination h

/-- The three-index elliptic relation. -/
def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

/-- `IsEllSequence` is equivalent to the universal `Rel₃` property. -/
lemma isEllSequence_iff_rel₃ : IsEllSequence W ↔ ∀ m n r : ℤ, Rel₃ W m n r := Iff.rfl

/-- The numerator of an invariant of an elliptic sequence, such that for each `s`,
`invarNum s n / invarDenom s n` is a constant independent of `n`. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

/-- The denominator of an invariant of an elliptic sequence. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [net]; ring_nf))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

lemma addMulSub_even (m n : ℤ) : addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]

lemma addMulSub_odd (m n : ℤ) :
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := by
  have h k := Int.mul_tdiv_cancel_left k two_ne_zero
  rw [addMulSub, ← h (m + n + 1), ← h (m - n)]; congr <;> ring

lemma addMulSub_same (zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0 := by
  rw [addMulSub, sub_self, Int.zero_tdiv, zero, mul_zero]

lemma addMulSub_neg₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W (-m) n = addMulSub W m n := by
  simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring

lemma addMulSub_neg₁ (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
  rw [addMulSub, addMulSub, mul_comm]; abel_nf

lemma addMulSub_abs₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W |m| n = addMulSub W m n := by
  obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]

lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring_nf

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_addMulSub (m n : ℤ) : f (addMulSub W m n) = addMulSub (f ∘ W) m n := by
  simp_rw [addMulSub, map_mul, Function.comp]

lemma map_rel₄ (p q r s : ℤ) : f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s := by
  simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]

lemma map_net (p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s := by
  simp_rw [net_eq_rel₄, map_rel₄]

lemma map_invarNum (s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp]

lemma map_invarDenom (s m : ℤ) : f (invarDenom W s m) = invarDenom (f ∘ W) s m := by
  simp_rw [invarDenom, map_mul, Function.comp]

end Map

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  rw [rel₄, ← mul_zero 2, Rel₃]
  simp_rw [addMulSub_even, add_zero, sub_zero]
  convert sub_eq_zero.symm using 2; ring

section transf

variable (a b c d : ℤ)

/-- The proposition that the four indices are all nonneg and strictly decreasing. -/
def StrictAnti₄ : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

/-- The proposition that the four indices are of the same parity. -/
def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

/-- The average of four indices. -/
def avg₄ : ℤ := (a + b + c + d) / 2

namespace HaveSameParity₄
open Int Equiv

variable {W a b c d} (same : HaveSameParity₄ a b c d)
include same

lemma rel₄_eq_net : rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  have h := @Int.two_mul_ediv_two_of_even
  rw [net_eq_rel₄, h, h, h]; · simp_rw [sub_add_cancel]
  all_goals rw [← negOnePow_eq_iff]
  exacts [same.2.2, same.2.1.trans same.2.2, same.1.trans (same.2.1.trans same.2.2)]

lemma even_sum : Even (a + b + c + d) := by
  simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
    same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]

lemma avg₄_add_avg₄ : avg₄ a b c d + avg₄ a b c d = a + b + c + d := by
  rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd

lemma same₀₃ : a.negOnePow = d.negOnePow := by rw [same.1, same.2.1, same.2.2]

protected lemma abs : HaveSameParity₄ |a| |b| |c| |d| := by
  simpa only [HaveSameParity₄, negOnePow_abs] using same

omit same in
lemma perm (σ : Perm (Fin 4)) :
    ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)) := by
  have hmem := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction
    (motive := fun σ _ ↦ ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)))
    ?_ (fun _ ↦ id) (fun σ τ _ _ hσ hτ t same ↦ ?_) hmem
  on_goal 2 => simp_rw [Perm.mul_apply]; exact hτ (t ∘ σ) (hσ _ same)
  rintro _ ⟨i, rfl⟩ t ⟨h₀₁, h₁₂, h₂₃⟩; fin_cases i
  exacts [⟨h₀₁.symm, h₀₁ ▸ h₁₂, h₂₃⟩,
    ⟨h₀₁ ▸ h₁₂, h₁₂.symm, h₁₂ ▸ h₂₃⟩,
    ⟨h₀₁, h₁₂ ▸ h₂₃, h₂₃.symm⟩]

lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
  simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  rw [← add_two_le_iff_lt_of_even_sub] at hdc hcb hba
  · linarith
  exacts [same.1, same.2.1, same.2.2]

variable (W) in
/-- A hybrid product formed by one factor from an `addMulSub` and one from another. -/
def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)

omit same in
lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub]; ring

lemma addMulSub_transf :
    addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - c) = addMulSub₄ W a b c d ∧
      addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - b) = addMulSub₄ W a c b d ∧
      addMulSub W (avg₄ a b c d - d) |avg₄ a b c d - a| = addMulSub₄ W b c a d ∧
      addMulSub W (avg₄ a b c d - c) (avg₄ a b c d - b) = addMulSub₄ W a d b c ∧
      addMulSub W (avg₄ a b c d - c) |avg₄ a b c d - a| = addMulSub₄ W b d a c ∧
      addMulSub W (avg₄ a b c d - b) |avg₄ a b c d - a| = addMulSub₄ W c d a b := by
  simp_rw [addMulSub_abs₁, addMulSub, addMulSub₄, sub_add_sub_comm, same.avg₄_add_avg₄]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf

theorem rel₄_transf :
    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf (W := W)
  simp_rw [rel₄, h₁, h₂, h₃, h₄, h₅, h₆, addMulSub₄_mul_addMulSub₄]; ring

theorem transf : HaveSameParity₄
    (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]

theorem strictAnti₄_transf (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b)
      |avg₄ a b c d - a| := by
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]
  · rw [sub_neg_eq_add, sub_add_sub_comm, same.avg₄_add_avg₄]; linarith only [hd, hdc]
  all_goals linarith only [hdc, hcb, hba]

end HaveSameParity₄

end transf

/-- The four-index elliptic relation multiplied by a two-index "coefficient". -/
abbrev rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d

@[simp] lemma rel₆_eq (k l a b c d : ℤ) :
    rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d := rfl

lemma rel₆_eq₃ (c d m n r : ℤ) :
    rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d := by
  simp_rw [rel₆, rel₄]; ring

lemma rel₆_eq₃' (c d m n r : ℤ) :
    rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d := by
  simp_rw [rel₆, rel₄]; ring

theorem rel₆_eq₁₀ (c d m n r s : ℤ) :
    rel₆ W c d m n r s =
      rel₆ W n d m r s c - rel₆ W r d m n s c + rel₆ W s d m n r c
      + rel₆ W n c m r s d - rel₆ W r c m n s d + rel₆ W s c m n r d
      + rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d
      - 2 * rel₆ W m d n r s c := by
  simp_rw [rel₆, rel₄]; ring

/-- The recurrence defining odd terms of an elliptic sequence. -/
def OddRec (m : ℤ) : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

/-- The recurrence defining even terms of an elliptic sequence. -/
def EvenRec (m : ℤ) : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
  rw [Rel₃, OddRec]; ring_nf

lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m := by
  rw [Rel₃, EvenRec]; ring_nf

lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  rw [iff_comm, EvenRec, ← sub_eq_zero, show 2 * m - 1 = 2 * (m - 1) + 1 by ring]
  have e₃₁ : addMulSub W 3 1 = W 2 * W 1 := by
    have h := addMulSub_odd (W := W) 1 0; norm_num at h; exact h
  have e₃ : ∀ k : ℤ, addMulSub W (2 * k + 1) 3 = W (k + 2) * W (k - 1) := fun k ↦ by
    have h := addMulSub_odd (W := W) k 1
    rw [show (2 * (1 : ℤ) + 1) = 3 by norm_num, show k + 1 + 1 = k + 2 by ring] at h
    exact h
  have e₁ : ∀ k : ℤ, addMulSub W (2 * k + 1) 1 = W (k + 1) * W k := fun k ↦ by
    have h := addMulSub_odd (W := W) k 0; norm_num at h; exact h
  simp only [rel₄, addMulSub_odd, e₃₁, e₃, e₁]
  ring_nf

/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
/-- The minimal possible third index in the four-index elliptic relation given the first index. -/
def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_nonneg (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two

lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h
  · simp [Int.negOnePow_even, h]
  · simp [Int.negOnePow_odd, Int.not_even_iff_odd.mp h]

lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]

variable {W}
lemma addMulSub_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]

lemma dMin_le {a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]

open Int

section Rel₄OfValid

variable (W) in
/-- The four-index elliptic relation restricted to valid (same-parity, strictly decreasing,
nonneg) quadruples. -/
def Rel₄OfValid (a b c d : ℤ) : Prop :=
  HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0

variable {a c₀ d₀ : ℤ} (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀)
  (lt : d₀ < c₀) (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀)
  (mem : addMulSub W c₀ d₀ ∈ R⁰)
include par le lt rel mem

lemma rel₄_fix₁_of_fix₂ (b c : ℤ) :
    Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀) := by
  refine ⟨fun same anti ↦ mem.2 _ ?_, fun _hc same anti ↦ mem.2 _ ?_⟩ <;>
    rw [mul_comm, ← rel₆_eq]
  on_goal 1 => rw [rel₆_eq₃]; have _hc := trivial
  on_goal 2 => rw [rel₆_eq₃']
  all_goals simp only [rel₆_eq]; rw [rel le_rfl, rel le_rfl, rel anti.2.2.2.le]
  iterate 2
    simp_rw [mul_zero, add_zero, sub_zero]
    iterate 3
      simp only [HaveSameParity₄, par, same.1, same.2.1, same.2.2, true_and]
      refine ⟨le, lt, ?_, ?_⟩ <;> linarith only [_hc, anti.2.1, anti.2.2.1, anti.2.2.2]

lemma rel₄_of_fix₂ (b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) :
    Rel₄OfValid W a b c d := fun same ⟨_, hdc, hcb, hba⟩ ↦ mem.2 _ <| by
  rw [mul_comm, ← rel₆_eq, rel₆_eq₁₀]; simp only [rel₆_eq]
  have fix₁ b c := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).1
  have fix₂ {b c} := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).2
  rw [fix₁, fix₁, fix₁, fix₂ hc, fix₂ hc, fix₂ (hc.trans hdc), rel le_rfl, rel le_rfl,
    rel le_rfl, (rel₄_fix₁_of_fix₂ par le lt (fun h ↦ rel <| h.trans hba.le) mem _ _).1]
  · simp_rw [mul_zero, add_zero, sub_zero]
  iterate 10
    simp only [HaveSameParity₄, par, par', same.1, same.2.1, same.2.2, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hc, le, lt, hdc, hcb, hba]

omit par le lt rel mem in
theorem rel₄_of_min₂ (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) :
    Rel₄OfValid W a b c d := fun same anti ↦ by
  obtain hc|hc := lt_or_ge (cMin a) d
  · refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
      (addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ same anti
    rw [negOnePow_dMin, same.1, same.2.1, same.2.2]
  have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a)
    rel (addMulSub_mem_nonZeroDivisors one two a) b c
  obtain rfl|hc := hc.eq_or_lt
  · exact fix.1 same anti
  obtain rfl : dMin a = d := (dMin_le same.same₀₃ anti.1).antisymm <| by
    rwa [← add_two_le_iff_lt_of_even_sub, cMin, add_le_add_iff_right] at hc
    rw [← negOnePow_eq_iff, negOnePow_cMin, same.same₀₃]
  obtain rfl|hc : cMin a = c ∨ _ := ((add_two_le_iff_lt_of_even_sub <| by
    rw [← negOnePow_eq_iff, negOnePow_dMin, same.1, same.2.1]).mpr anti.2.1).eq_or_lt
  exacts [rel le_rfl same anti, fix.2 hc same anti]

omit par le lt rel mem in
theorem rel₄_of_anti_oddRec_evenRec (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m, 2 ≤ m → OddRec W m) (evenRec : ∀ m, 3 ≤ m → EvenRec W m) :
    ∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d :=
  Int.strongRec (m := 6)
    (fun a ha b c d same anti ↦ absurd ha (not_lt.mpr (same.six_le_of_strictAnti₄ anti)))
    fun a h6 ih ↦ rel₄_of_min₂ one two fun {a' b} haa same anti ↦ by
  obtain ha'|ha' := lt_or_eq_of_le haa
  · exact ih _ ha' same anti
  obtain hba|rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (add_two_le_iff_lt_of_even_sub <| (negOnePow_eq_iff _ _).1 same.1).mpr anti.2.2.2
  · rw [← same.rel₄_transf]
    refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)
    rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
    linarith only [hba]
  obtain ⟨m, rfl|rfl⟩ := b.even_or_odd'
  · have ea : Even a := by rw [← ha']; exact (even_two_mul _).add even_two
    simp_rw [cMin, dMin, if_pos ea]
    convert (rel₃_iff₄ W (m + 1) m 1).mp ((rel₃_iff_oddRec W m).mpr <| oddRec _ ?_) using 2
    all_goals linarith only [h6, ha']
  · have nea : ¬ Even a := by
      rw [← ha', not_even_iff_odd]; convert odd_two_mul_add_one (m + 1) using 1; ring
    simp_rw [cMin, dMin, if_neg nea]
    convert (rel₄_iff_evenRec W (m + 1)).mpr (evenRec _ ?_) using 2
    all_goals linarith only [h6, ha']

end Rel₄OfValid

section Perm

variable (neg : ∀ k, W (-k) = -W k)
include neg

lemma rel₄_abs {m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]

lemma rel₄_swap₀₁ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W n m r s := by
  simp_rw [rel₄, addMulSub_swap W neg n m]; ring

lemma rel₄_swap₁₂ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m r n s := by
  simp_rw [rel₄, addMulSub_swap W neg r n]; ring

lemma rel₄_swap₂₃ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m n s r := by
  simp_rw [rel₄, addMulSub_swap W neg s r]; ring

open Equiv

variable (W) in
/-- The four-index elliptic relation with a tuple as input. -/
def relFin4 (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)

/-- `rel₄` is invariant (up to sign) under permutation of the four indices. -/
theorem relFin4_perm (σ : Perm (Fin 4)) :
    ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t := by
  have hmem := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction
    (motive := fun (σ : Perm (Fin 4)) _ ↦ ∀ t,
      relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t)
    ?_ (fun t ↦ by simp) (fun σ τ _ _ hσ hτ t ↦ ?_) hmem
  on_goal 2 =>
    rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ, map_mul, mul_comm, mul_smul]
  rintro _ ⟨i, rfl⟩ t; fin_cases i <;>
    rw [Perm.sign_swap Fin.castSucc_lt_succ.ne, Units.neg_smul, one_smul]
  exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]

lemma relFin4_perm' (σ : Perm (Fin 4)) (t) :
    Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]

variable (zero : W 0 = 0)
include zero

omit neg in
lemma rel₄_same₀₁ (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

omit neg in
lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

omit neg in
lemma rel₄_same₂₃ (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (oddRec : ∀ m, 2 ≤ m → OddRec W m) (evenRec : ∀ m, 3 ≤ m → EvenRec W m)
include one two oddRec evenRec

theorem rel₄_of_oddRec_evenRec {a b c d : ℤ} (same : HaveSameParity₄ a b c d) :
    rel₄ W a b c d = 0 := by
  let t : Fin 4 → ℤ := fun i ↦ match i with
    | 0 => |a|
    | 1 => |b|
    | 2 => |c|
    | 3 => |d|
  have nonneg i : 0 ≤ t i := by fin_cases i <;> exact abs_nonneg _
  let σ := Fin.revPerm.trans (Tuple.sort t)
  have anti : Antitone (t ∘ σ) := by
    simp_rw [σ, coe_trans, ← Function.comp_assoc]
    exact (Tuple.monotone_sort t).comp_antitone fun _ _ ↦ Fin.rev_le_rev.mpr
  clear_value σ
  rw [← rel₄_abs neg]; change relFin4 W t = 0
  rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]
  by_cases h₃₂ : t (σ 3) = t (σ 2); · rw [h₃₂, rel₄_same₂₃ zero, smul_zero]
  by_cases h₂₁ : t (σ 2) = t (σ 1); · rw [h₂₁, rel₄_same₁₂ zero, smul_zero]
  by_cases h₁₀ : t (σ 1) = t (σ 0); · rw [h₁₀, rel₄_same₀₁ zero, smul_zero]
  rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec
    (HaveSameParity₄.perm σ t same.abs), smul_zero]
  exact ⟨nonneg _, (anti <| by decide).lt_of_ne h₃₂,
    (anti <| by decide).lt_of_ne h₂₁, (anti <| by decide).lt_of_ne h₁₀⟩

/-- An ℕ-indexed sequence satisfying the even-odd recurrence, after extension to all integers
by symmetry (to make an odd function), is an elliptic sequence, provided its first two terms
are not zero divisors. -/
theorem _root_.IsEllSequence.of_oddRec_evenRec : IsEllSequence W := fun m n r ↦ by
  change Rel₃ W m n r
  rw [rel₃_iff₄, rel₄_of_oddRec_evenRec neg zero one two oddRec evenRec]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [negOnePow_two_mul, negOnePow_zero]

end Perm

end EllSequence

open EllSequence

namespace IsEllSequence

variable {R : Type*} [CommRing R] {W : ℤ → R} (ell : IsEllSequence W)
include ell

lemma oddRec (m : ℤ) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)
lemma evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)

/-- The zeroth term of an elliptic sequence is zero,
provided some even term is not a zero divisor. -/
lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have h := ell m m (2 * m)
  rw [show m + m = 2 * m by ring, sub_self] at h
  -- h : W (2*m) * W 0 * W (2*m)^2 = X - X, so the RHS is zero
  have h' : W (2 * m) * W 0 * W (2 * m) ^ 2 = 0 := by
    have : W (m + 2 * m) * W (m - 2 * m) * W m ^ 2 -
      W (m + 2 * m) * W (m - 2 * m) * W m ^ 2 = 0 := sub_self _
    rw [h, this]
  have h'' : W 0 * (W (2 * m) * W (2 * m) ^ 2) = 0 := by linear_combination h'
  rw [mul_comm (W (2 * m)) (W (2 * m) ^ 2), ← pow_succ] at h''
  exact (pow_mem mem 3).2 _ h''

lemma sub_add_neg_sub_mul_eq_zero (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have := congr($(ell m n r) + $(ell n m r))
  rw [add_comm n, ← right_distrib, ← left_distrib, mul_comm (W _)] at this
  rw [show (-(m - n) : ℤ) = n - m by ring]
  convert this using 1; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
include one two

/-- An elliptic sequence is an odd function, provided its first two terms are not zero divisors. -/
lemma neg (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  · refine two.2 _ ((pow_mem one 2).2 _ ?_)
    have := sub_add_neg_sub_mul_eq_zero ell (1 - ↑m) (↑m + 1) 1
    rw [show ((1 : ℤ) - ↑m - (↑m + 1)) = -(2 * ↑m) by lia,
      show ((1 : ℤ) - ↑m + (↑m + 1)) = 2 by lia] at this
    simpa [neg_neg] using this
  · refine one.2 _ ((pow_mem one 2).2 _ ?_)
    have := sub_add_neg_sub_mul_eq_zero ell (-↑m) (↑m + 1) 1
    rw [show ((-↑m : ℤ) - (↑m + 1)) = -(2 * ↑m + 1) by lia,
      show ((-↑m : ℤ) + (↑m + 1)) = 1 by lia] at this
    simpa [neg_neg] using this

protected lemma rel₄ {a b c d : ℤ} (same : HaveSameParity₄ a b c d) :
    EllSequence.rel₄ W a b c d = 0 :=
  rel₄_of_oddRec_evenRec (ell.neg one two) (ell.zero 1 two) one two
    (fun _ _ ↦ ell.oddRec _) (fun _ _ ↦ ell.evenRec _) same

protected lemma net (p q r s : ℤ) : EllSequence.net W p q r s = 0 := by
  rw [net_eq_rel₄]
  refine ell.rel₄ one two ?_
  simp_rw [HaveSameParity₄, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, true_and]

lemma invar (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invar_of_net _ (ell.net one two) _ _ _

end IsEllSequence

section NormEDSOfMem

variable {R : Type*} [CommRing R] (b c d : R)

private theorem normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) :
    IsEllSequence (normEDS b c d) := by
  refine IsEllSequence.of_oddRec_evenRec (normEDS_neg _ _ _) (normEDS_zero _ _ _)
    (by rw [normEDS_one]; exact one_mem _) (by rwa [normEDS_two]) ?_ ?_ <;>
    intro m hm <;> rw [← sub_nonneg] at hm
  · lift m - 2 to ℕ using hm with k hk
    rw [← eq_sub_iff_add_eq.mp hk, OddRec, normEDS_one, one_pow, mul_one]
    have h := normEDS_odd b c d (↑k + 2)
    convert h using 2
  · lift m - 3 to ℕ using hm with k hk
    rw [← eq_sub_iff_add_eq.mp hk, EvenRec, normEDS_one, normEDS_two, one_pow, mul_one]
    convert normEDS_even b c d (↑k + 3) using 1
    ring

end NormEDSOfMem

section NormEDSLemmas

variable {R : Type*} [CommRing R] (b c d : R)

lemma invarNum_normEDS (n : ℤ) : letI W := normEDS b c d
    EllSequence.invarNum W 1 n =
      W (n + 2) * W (n - 1) ^ 2 + W (n + 1) ^ 2 * W (n - 2) + W n ^ 3 * b ^ 2 := by
  simp [EllSequence.invarNum]

lemma invarNum_normEDS_two :
    EllSequence.invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [EllSequence.invarNum, right_distrib, ← pow_succ, ← pow_add]

lemma invarDenom_normEDS_two :
    EllSequence.invarDenom (normEDS b c d) 1 2 = c * b := by
  simp [EllSequence.invarDenom]

lemma normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_complEDS₂, complEDS₂, if_neg (by decide)]
  simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]
  rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, if_neg (by decide)]
  ring

end NormEDSLemmas

section Universal

variable {R : Type*} [CommRing R] (b c d : R)

/-- A type of three elements corresponding to the three parameters of a normalised EDS. -/
inductive Param : Type | B : Param | C : Param | D : Param

open Param MvPolynomial

/-- The universal normalised EDS, from which every normalised EDS can be obtained by
composing with a ring homomorphism. -/
noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)

lemma normEDS_eq_aeval :
    normEDS b c d = (MvPolynomial.aeval (Param.rec b c d) <| universalNormEDS ·) := by
  funext n
  unfold universalNormEDS
  simp [MvPolynomial.aeval]

lemma complEDS₂_eq_aeval :
    complEDS₂ b c d =
      (MvPolynomial.aeval (Param.rec b c d) <| complEDS₂ (X (R := ℤ) B) (X C) (X D) ·) := by
  funext n
  simp [MvPolynomial.aeval]

lemma complEDS_eq_aeval :
    complEDS b c d =
      (MvPolynomial.aeval (Param.rec b c d) <| complEDS (X (R := ℤ) B) (X C) (X D) · ·) := by
  funext m n
  simp [MvPolynomial.aeval]

end Universal

section NormEDSIsEll

variable {R : Type*} [CommRing R] (b c d : R)
open Param MvPolynomial

private lemma IsEllSequence.map' {S : Type*} [CommRing S] {W : ℤ → R} (h : IsEllSequence W)
    (f : R →+* S) : IsEllSequence (f ∘ W) := by
  intro m n r
  simpa [Function.comp] using congr_arg f (h m n r)

/-- A normalised EDS is an elliptic sequence. -/
protected theorem IsEllSequence.normEDS : IsEllSequence (normEDS b c d) := by
  rw [normEDS_eq_aeval]
  exact map' (normEDS_of_mem_nonZeroDivisors _ _ _
    (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _)) _

end NormEDSIsEll

section Ext

variable {R : Type*} [CommRing R] {W U : ℤ → R}

/-- Two elliptic sequences with the same first four terms are equal,
provided the first two terms are non-zero-divisors. -/
protected theorem IsEllSequence.ext (ellW : IsEllSequence W) (ellU : IsEllSequence U)
    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U :=
  funext fun n ↦ by
    induction n using Int.negInduction with
    | nat n =>
      refine normEDSRec ?_ h1 h2 h3 h4 (fun m h₁ h₂ h₃ h₄ h₅ ↦ ?_)
        (fun m h₁ h₂ h₃ h₄ ↦ ?_) n
      · rw [Nat.cast_zero, ellW.zero 1 two, ellU.zero 1 (h2 ▸ two)]
      · erw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two <| pow_mem one 2),
          ← mul_assoc, ← mul_assoc, Nat.cast_mul, Nat.cast_add, ellW.evenRec, h1, h2,
          ellU.evenRec]
        convert congr($h₃ * ($h₂ ^ 2 * $h₅ - $h₁ * $h₄ ^ 2)) <;> abel
      · rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
        erw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, ellW.oddRec, h1, ellU.oddRec]
        convert congr($h₄ * $h₂ ^ 3 - $h₁ * $h₃ ^ 3) <;> abel
    | neg hn n =>
      rw [ellW.neg one two, ellU.neg (h1 ▸ one) (h2 ▸ two), hn]

end Ext

section CuspEval

/-- When `b = 2, c = 3, d = 2`, the normalised EDS is the identity. -/
lemma normEDS_two_three_two : normEDS (2 : ℤ) 3 2 = id := by
  apply IsEllSequence.ext (IsEllSequence.normEDS 2 3 2) isEllSequence_id <;>
    simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  exacts [mem_nonZeroDivisors_of_ne_zero one_ne_zero,
    mem_nonZeroDivisors_of_ne_zero two_ne_zero, rfl, rfl, rfl, rfl]

/-- When `b = 2, c = 3, d = 2`, the 2-complement is constantly 2. -/
lemma complEDS₂_two_three_two (n : ℤ) : complEDS₂ (2 : ℤ) 3 2 n = 2 := by
  obtain rfl | hn := eq_or_ne n 0
  · exact complEDS₂_zero ..
  · have := normEDS_mul_complEDS₂ (2 : ℤ) 3 2 n
    rw [normEDS_two_three_two] at this
    simp only [id] at this
    exact mul_right_cancel₀ hn (by linarith)

open Param MvPolynomial in
private lemma universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 :=
  fun h ↦ hn <| by
    have : normEDS (2 : ℤ) 3 2 n = 0 := by
      have h' := congr_arg (aeval (Param.rec (2 : ℤ) 3 2)) h
      rw [map_zero] at h'
      rwa [show (aeval (Param.rec (2 : ℤ) 3 2)) (universalNormEDS n) =
        normEDS (2 : ℤ) 3 2 n from (congr_fun (normEDS_eq_aeval (2 : ℤ) 3 2) n).symm] at h'
    rwa [normEDS_two_three_two, id] at this

private lemma universalNormEDS_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :
    universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)

end CuspEval

section NormEDSMulComplEDS

variable {R : Type*} [CommRing R] (b c d : R)

private lemma normEDS_mul_complEDS_of_mem (hb : b ∈ R⁰) {m : ℤ}
    (hm : normEDS b c d m ∈ R⁰) (n : ℤ) :
    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) := by
  have ellW := IsEllSequence.normEDS b c d
  have hmem1 : normEDS b c d 1 ∈ R⁰ := by rw [normEDS_one]; exact one_mem _
  have hmem2 : normEDS b c d 2 ∈ R⁰ := by rw [normEDS_two]; exact hb
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _ | n := n
    · simp [complEDS_zero, ellW.zero 1 hmem2]
    obtain _ | n := n
    · simp [complEDS_one]
    rw [complEDS_ofNat]
    obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by lia, complEDS'_even]
      have step1 : normEDS b c d m * complEDS b c d m ↑(k + 1) =
          normEDS b c d (↑(k + 1) * m) := ih _ (by lia)
      calc normEDS b c d m * (complEDS' b c d m (k + 1) *
              complEDS₂ b c d ((↑k + 1) * m))
          = normEDS b c d m * complEDS' b c d m (k + 1) *
              complEDS₂ b c d (↑(k + 1) * m) := by push_cast; ring
        _ = normEDS b c d (↑(k + 1) * m) *
              complEDS₂ b c d (↑(k + 1) * m) := by
            congr 1; rw [← complEDS_ofNat]; exact step1
        _ = normEDS b c d (2 * (↑(k + 1) * m)) := normEDS_mul_complEDS₂ ..
        _ = normEDS b c d (↑(2 * (k + 1)) * m) := by push_cast; ring_nf
    · rw [show 2 * k + 1 + 1 + 1 = 2 * (k + 1) + 1 by lia, complEDS'_odd]
      rw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem hm (pow_mem hmem1 2))]
      have h := (ellW ((↑k + 2) * m) ((↑k + 1) * m) 1).symm
      simp only [normEDS_one, one_pow, mul_one] at h
      have ih1 : normEDS b c d m * complEDS' b c d m (k + 1) =
          normEDS b c d ((↑k + 1) * m) := by
        have := ih (k + 1) (by lia); rwa [complEDS_ofNat, Nat.cast_succ] at this
      have ih2 : normEDS b c d m * complEDS' b c d m (k + 2) =
          normEDS b c d ((↑k + 2) * m) := by
        have := ih (k + 2) (by lia)
        rwa [complEDS_ofNat, show (↑(k + 2) : ℤ) = ↑k + 2 by push_cast; ring] at this
      simp only [normEDS_one, one_pow, mul_one] at h ⊢
      rw [show (↑k + 2) * m + (↑k + 1) * m = (↑(2 * (k + 1) + 1) : ℤ) * m by
          push_cast; ring,
        show (↑k + 2) * m - (↑k + 1) * m = m by ring] at h
      rw [← ih1, ← ih2] at h
      linear_combination h
  | neg hn n =>
    rw [neg_mul, normEDS_neg, complEDS_neg, mul_neg, hn n]

open Param MvPolynomial in
lemma normEDS_mul_complEDS (m n : ℤ) :
    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [normEDS_zero, mul_comm n 0]
  · have h := normEDS_mul_complEDS_of_mem
      (b := X (R := ℤ) B) (c := X C) (d := X D)
      (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _)
      (universalNormEDS_mem_nonZeroDivisors hm) n
    have h' := congr_arg (aeval (Param.rec b c d)) h
    rw [map_mul] at h'
    rwa [show aeval (Param.rec b c d) (normEDS (X B) (X C) (X D) m) =
        normEDS b c d m from (congr_fun (normEDS_eq_aeval b c d) m).symm,
      show aeval (Param.rec b c d) (complEDS (X B) (X C) (X D) m n) =
        complEDS b c d m n from (congr_fun₂ (complEDS_eq_aeval b c d) m n).symm,
      show aeval (Param.rec b c d) (normEDS (X B) (X C) (X D) (n * m)) =
        normEDS b c d (n * m) from (congr_fun (normEDS_eq_aeval b c d) (n * m)).symm] at h'

lemma normEDS_mul_complEDS_div {m : ℤ} (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :
    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n := by
  obtain ⟨n, rfl⟩ := dvd
  rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]

end NormEDSMulComplEDS

section ComplEDSAux₂

variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)

/-- The auxiliary complement, used in the `ω` definition. -/
def complEDSAux₂ : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] lemma complEDSAux₂_zero : complEDSAux₂ b c d 0 = -1 := by simp [complEDSAux₂]
@[simp] lemma complEDSAux₂_one : complEDSAux₂ b c d 1 = -b := by simp [complEDSAux₂]
@[simp] lemma complEDSAux₂_neg_one : complEDSAux₂ b c d (-1) = 0 := by simp [complEDSAux₂]
@[simp] lemma complEDSAux₂_two : complEDSAux₂ b c d 2 = 0 := by simp [complEDSAux₂]
@[simp] lemma complEDSAux₂_neg_two : complEDSAux₂ b c d (-2) = -d := by simp [complEDSAux₂]

lemma complEDSAux₂_mul_b :
    complEDSAux₂ b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [complEDSAux₂, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]; split_ifs <;> ring

lemma complEDSAux₂_neg :
    complEDSAux₂ b c d (-m) = -complEDS₂ b c d m - complEDSAux₂ b c d m := by
  simp_rw [complEDSAux₂, complEDS₂, neg_sub_left, neg_add_eq_sub, ← neg_sub m,
    preNormEDS_neg, even_neg]; ring_nf

variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_complEDSAux₂ : complEDSAux₂ (f b) (f c) (f d) m = f (complEDSAux₂ b c d m) := by
  simp only [complEDSAux₂, map_preNormEDS, map_mul, map_pow, map_one, apply_ite f]

end ComplEDSAux₂

section RedInvar

variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)

/-- The reduced invariant numerator. -/
def redInvarNum : R :=
  complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDSAux₂ b c d m

lemma complEDS₂_eq_redInvarNum_sub :
    complEDS₂ b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * complEDSAux₂ b c d m := by
  rw [redInvarNum]; ring

lemma invarNum_eq_redInvarNum_mul :
    EllSequence.invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b,
    complEDSAux₂_mul_b, invarNum_normEDS]; ring

/-- The reduced invariant denominator. -/
def redInvarDenom : R :=
  let C := complEDS b c d
  let W := normEDS b c d
  let r₆ := normEDS b c d 5 - d ^ 2
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0

lemma invarDenom_normEDS_eq_redInvarDenom_mul :
    EllSequence.invarDenom (normEDS b c d) 1 m =
      redInvarDenom b c d m * b * c := by
  have h6 : (6 : ℤ) ≠ 0 := by decide
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hd k m' dvd eq :=
    (@Int.dvd_iff_emod_eq_zero k m').mpr ((@Int.emod_emod_of_dvd m' k 6 dvd).symm.trans eq)
  have hd2 {m' : ℤ} := hd 2 m' ⟨3, rfl⟩
  have hd3 {m' : ℤ} := hd 3 m' ⟨2, rfl⟩
  -- Helper: replace normEDS b c d n by normEDS b c d k * complEDS b c d k (n/k) when k | n
  have replace6 {n : ℤ} (dvd : (6 : ℤ) ∣ n) :
    normEDS b c d n = normEDS b c d 6 * complEDS b c d 6 (n / 6) :=
    (normEDS_mul_complEDS_div b c d h6 n dvd).symm
  have replace3 {n : ℤ} (dvd : (3 : ℤ) ∣ n) :
    normEDS b c d n = normEDS b c d 3 * complEDS b c d 3 (n / 3) :=
    (normEDS_mul_complEDS_div b c d h3 n dvd).symm
  have replace2 {n : ℤ} (dvd : (2 : ℤ) ∣ n) :
    normEDS b c d n = normEDS b c d 2 * complEDS b c d 2 (n / 2) :=
    (normEDS_mul_complEDS_div b c d two_ne_zero n dvd).symm
  rw [EllSequence.invarDenom, redInvarDenom]; split_ifs with h h h h h h
  · rw [replace6 (Int.dvd_of_emod_eq_zero h), normEDS_six_eq_mul]; ring
  · rw [replace6 (Int.dvd_self_sub_of_emod_eq h), normEDS_six_eq_mul]; ring
  · rw [show m + 1 = m + 6 - 5 by abel,
      replace6 (Int.dvd_self_sub_of_emod_eq (Int.emod_eq_add_self_emod.symm.trans h)),
      normEDS_six_eq_mul]; ring
  on_goal 1 =>
    have d3 : 3 ∣ (m + 1) := hd3 (by rw [Int.add_emod, h]; decide)
    have d2 : 2 ∣ m := hd2 (by rw [h]; decide)
    rw [replace3 d3, replace2 d2]
  on_goal 2 =>
    have d3 : 3 ∣ (m - 1) := hd3 (by rw [Int.sub_emod, h]; decide)
    have d2 : 2 ∣ m := hd2 (by rw [h]; decide)
    rw [replace3 d3, replace2 d2]
  on_goal 3 =>
    have d3 : 3 ∣ m := hd3 (by rw [h]; decide)
    have d2 : 2 ∣ (m - 1) := hd2 (by rw [Int.sub_emod, h]; decide)
    rw [replace3 d3, replace2 d2]
  on_goal 4 =>
    have h0 := Int.emod_nonneg m h6
    have lt := Int.emod_lt_of_pos m (show 0 < 6 by decide)
    interval_cases m % 6 <;> contradiction
  all_goals rw [normEDS_three, normEDS_two]; ring

@[simp] lemma redInvarDenom_zero : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom]

@[simp] lemma redInvarDenom_one : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom]

@[simp] lemma redInvarDenom_two : redInvarDenom b c d 2 = 1 := by
  simp [redInvarDenom]

variable {S : Type*} [CommRing S] (f : R →+* S)

lemma map_redInvarNum : redInvarNum (f b) (f c) (f d) m = f (redInvarNum b c d m) := by
  simp only [redInvarNum, map_add, map_mul, map_pow, map_ofNat,
    ← map_complEDS₂, ← map_normEDS, ← map_complEDSAux₂]

lemma map_redInvarDenom : redInvarDenom (f b) (f c) (f d) m = f (redInvarDenom b c d m) := by
  simp only [redInvarDenom, ← map_normEDS, ← map_complEDS, map_sub, map_pow, map_mul,
    apply_ite f, map_zero]

end RedInvar

section NetInvarNormEDS

variable {R : Type*} [CommRing R] (b c d : R)
open Param MvPolynomial

/-- The net relation holds for normalised EDS. -/
lemma net_normEDS (p q r s : ℤ) : EllSequence.net (normEDS b c d) p q r s = 0 := by
  have ellU := IsEllSequence.normEDS (X (R := ℤ) B) (X C) (X D)
  have one : normEDS (X (R := ℤ) B) (X C) (X D) 1 ∈ _ ⁰ := by
    rw [normEDS_one]; exact one_mem _
  have two : normEDS (X (R := ℤ) B) (X C) (X D) 2 ∈ _ ⁰ :=
    mem_nonZeroDivisors_of_ne_zero <| by rw [normEDS_two]; exact X_ne_zero _
  have h := ellU.net one two p q r s
  rw [normEDS_eq_aeval]
  change EllSequence.net
    (((aeval (Param.rec b c d) : MvPolynomial Param ℤ →ₐ[ℤ] R).toRingHom) ∘
      universalNormEDS) p q r s = 0
  rw [← EllSequence.map_net, universalNormEDS, h, map_zero]

lemma invar_normEDS (s m n : ℤ) :
    EllSequence.invarNum (normEDS b c d) s m * EllSequence.invarDenom (normEDS b c d) s n =
      EllSequence.invarNum (normEDS b c d) s n * EllSequence.invarDenom (normEDS b c d) s m :=
  EllSequence.invar_of_net _ (net_normEDS b c d) _ _ _

private lemma invar₂_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (m : ℤ) :
    EllSequence.invarNum (normEDS b c d) 1 m * c =
      EllSequence.invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, mul_assoc, mul_assoc,
    mul_comm (EllSequence.invarDenom _ _ _)]
  convert invar_normEDS b c d 1 m (2 : ℤ) <;>
    simp only [invarNum_normEDS_two, invarDenom_normEDS_two]

lemma invar₂_normEDS {m : ℤ} :
    EllSequence.invarNum (normEDS b c d) 1 m * c =
      EllSequence.invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have heval : ∀ n, aeval (Param.rec b c d) (normEDS (X B) (X Param.C) (X D) n) =
      normEDS b c d n := fun n ↦ by
    change (aeval (Param.rec b c d)) (universalNormEDS n) = normEDS b c d n
    exact (congr_fun (normEDS_eq_aeval b c d) n).symm
  have h := invar₂_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) B) (c := X Param.C) (d := X D)
    (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero B) m
  have h' := congr_arg (aeval (Param.rec b c d)) h
  simp only [map_mul, map_add, map_pow, aeval_X, EllSequence.invarNum,
    EllSequence.invarDenom] at h'
  simp only [heval] at h'
  convert h' using 1 <;>
    simp only [EllSequence.invarNum, EllSequence.invarDenom]

private lemma redInvar_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (hc : c ∈ R⁰)
    (m : ℤ) : redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_normEDS_eq_redInvarDenom_mul]
  ring

/-- The reduced invariant identity for normalised EDS. -/
lemma redInvar_normEDS (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have h := congr_arg (aeval (Param.rec b c d)) (redInvar_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) B) (c := X Param.C) (d := X D) ?_ ?_ m)
  · have mapN := map_redInvarNum (X (R := ℤ) B) (X Param.C) (X D) m
      ((aeval (Param.rec b c d)).toRingHom)
    have mapD := map_redInvarDenom (X (R := ℤ) B) (X Param.C) (X D) m
      ((aeval (Param.rec b c d)).toRingHom)
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X] at mapN mapD
    rw [map_mul, map_add, map_pow, aeval_X, aeval_X] at h
    rw [← mapN, ← mapD] at h
    exact h
  all_goals exact mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)

end NetInvarNormEDS

section Divisibility

variable {R : Type*} [CommRing R] (b c d : R)

/-- A normalised EDS is a divisibility sequence. -/
protected theorem IsDivSequence.normEDS : IsDivSequence (normEDS b c d) := by
  intro m n ⟨k, hk⟩
  rw [hk, mul_comm m k]
  exact ⟨_, (normEDS_mul_complEDS b c d m k).symm⟩

/-- A normalised EDS is an EDS. -/
protected theorem IsEllDivSequence.normEDS : IsEllDivSequence (normEDS b c d) :=
  ⟨IsEllSequence.normEDS b c d, IsDivSequence.normEDS b c d⟩

end Divisibility

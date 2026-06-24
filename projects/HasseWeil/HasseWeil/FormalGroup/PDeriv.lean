import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Partial derivatives of multivariate formal power series

This file defines the formal partial derivative `MvPowerSeries.pderiv s` on
`MvPowerSeries σ R`. Mathlib provides a univariate version
`PowerSeries.derivative` for `PowerSeries R` and a polynomial version
`MvPolynomial.pderiv`, but there is no `pderiv` for multivariate power series.

The derivative is defined by the convention

  `pderiv s f  :=  ∑_d ((d s + 1) • coeff_{d + e_s} f) · X^d`,

which matches the univariate `PowerSeries.derivativeFun` for `σ = Unit` and
agrees with `MvPolynomial.pderiv` under the coercion
`MvPolynomial σ R → MvPowerSeries σ R` (see `pderiv_coe`).

This is used downstream in the proof of Silverman IV.4.2 (translation
invariance of the invariant differential on a formal group).

## Main definitions and results

* `MvPowerSeries.pderiv s f` — partial derivative w.r.t. `s : σ`.
* `MvPowerSeries.coeff_pderiv` — the coefficient of the derivative.
* `MvPowerSeries.pderiv_add`, `pderiv_zero`, `pderiv_smul`, `pderiv_C`,
  `pderiv_X_self`, `pderiv_X_of_ne`, `pderiv_sub`, `pderiv_neg`, `pderiv_one`
  — basic API.
* `MvPowerSeries.pderiv_monomial` — the derivative of a monomial.
* `MvPowerSeries.pderiv_mul` — **Leibniz rule** for the multivariate formal
  derivative.
* `MvPowerSeries.pderiv_coe` — agreement with `MvPolynomial.pderiv`.
* `MvPowerSeries.continuous_pderiv` — continuity of `pderiv` in the product
  topology.
* `MvPowerSeries.pderiv_subst` — **substitution chain rule** for
  `MvPowerSeries.pderiv` over a finite index type.
* `MvPowerSeries.pderiv_subst_fin2` — specialization to `σ = Fin 2`, as used
  in Silverman IV.4.2.
-/

noncomputable section

namespace MvPowerSeries

open Finsupp

variable {σ : Type*} {R : Type*}

/-! ### Definition and coefficient formula -/

section CommSemiring

variable [CommSemiring R]

/-- The formal partial derivative of a multivariate power series with
respect to the variable `s`. Concretely, the coefficient of `X^d` in
`pderiv s f` is `(d s + 1) * coeff_{d + e_s} f`, where `e_s = single s 1`. -/
def pderiv (s : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ (d s + 1 : ℕ) • coeff (R := R) (d + Finsupp.single s 1) f

@[simp]
theorem coeff_pderiv (s : σ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff (R := R) d (pderiv s f) =
      (d s + 1 : ℕ) • coeff (R := R) (d + Finsupp.single s 1) f :=
  rfl

/-! ### Additive / linear API -/

@[simp]
theorem pderiv_zero (s : σ) : pderiv s (0 : MvPowerSeries σ R) = 0 := by
  ext d
  simp [coeff_pderiv]

theorem pderiv_add (s : σ) (f g : MvPowerSeries σ R) :
    pderiv s (f + g) = pderiv s f + pderiv s g := by
  ext d
  simp [coeff_pderiv, map_add, smul_add]

theorem pderiv_smul (s : σ) (r : R) (f : MvPowerSeries σ R) :
    pderiv s (r • f) = r • pderiv s f := by
  ext d
  simp only [coeff_pderiv, coeff_smul]
  ring

private lemma single_self_apply (s : σ) :
    (Finsupp.single s (1 : ℕ)) s = 1 := by
  classical
  simp

private lemma add_single_ne_zero (d : σ →₀ ℕ) (s : σ) :
    d + Finsupp.single s 1 ≠ 0 := by
  intro h
  have hs := congrArg (fun f : σ →₀ ℕ ↦ f s) h
  simp at hs

@[simp]
theorem pderiv_one (s : σ) : pderiv s (1 : MvPowerSeries σ R) = 0 := by
  classical
  ext d
  rw [coeff_pderiv, coeff_one, if_neg (add_single_ne_zero d s), smul_zero, coeff_zero]

@[simp]
theorem pderiv_C (s : σ) (r : R) : pderiv s (C (σ := σ) r) = 0 := by
  classical
  ext d
  rw [coeff_pderiv, coeff_C, if_neg (add_single_ne_zero d s), smul_zero, coeff_zero]

@[simp]
theorem pderiv_X_self (s : σ) : pderiv s (X s : MvPowerSeries σ R) = 1 := by
  classical
  ext d
  rw [coeff_pderiv, coeff_X, coeff_one]
  by_cases hd : d = 0
  · subst hd
    have h : (0 : σ →₀ ℕ) + Finsupp.single s 1 = Finsupp.single s 1 := by simp
    rw [h, if_pos rfl, if_pos rfl, Finsupp.coe_zero, Pi.zero_apply, zero_add, one_smul]
  · have h : d + Finsupp.single s 1 ≠ Finsupp.single s 1 := by
      intro heq
      apply hd
      have : d + Finsupp.single s 1 = 0 + Finsupp.single s 1 := by
        rw [heq, zero_add]
      exact add_right_cancel this
    rw [if_neg h, if_neg hd, smul_zero]

@[simp]
theorem pderiv_X_of_ne {s t : σ} (h : s ≠ t) :
    pderiv s (X t : MvPowerSeries σ R) = 0 := by
  classical
  ext d
  rw [coeff_pderiv, coeff_X, coeff_zero]
  have h' : d + Finsupp.single s 1 ≠ Finsupp.single t (1 : ℕ) := by
    intro heq
    have hs : (d + Finsupp.single s 1 : σ →₀ ℕ) s = (Finsupp.single t (1 : ℕ)) s := by
      rw [heq]
    rw [Finsupp.add_apply, single_self_apply,
        Finsupp.single_apply, if_neg h.symm] at hs
    omega
  rw [if_neg h', smul_zero]

/-! ### Leibniz rule -/

/-- Auxiliary: `(a s) • x = 0` whenever `¬ single s 1 ≤ a`. -/
private lemma smul_eq_zero_of_not_le {s : σ} {a : σ →₀ ℕ}
    (h : ¬ Finsupp.single s 1 ≤ a) (x : R) :
    (a s : ℕ) • x = 0 := by
  classical
  have : a s = 0 := by
    by_contra hne
    apply h
    intro i
    by_cases hi : i = s
    · subst hi
      rw [single_self_apply]
      exact Nat.one_le_iff_ne_zero.mpr hne
    · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      exact Nat.zero_le _
  rw [this]
  simp

/-- The summand `(p.1 s) • (coeff p.1 f * coeff p.2 g)` vanishes unless
`single s 1 ≤ p.1`, so summing it over the antidiagonal of `d + single s 1`
agrees with summing it over only those terms with `single s 1 ≤ p.1`. This is
the "filter is harmless" step in the left half of the Leibniz rule. -/
private theorem sum_antidiagonal_smul_fst_eq_filter [DecidableEq σ] (s : σ)
    (f g : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    (∑ p ∈ Finset.antidiagonal (d + (Finsupp.single s 1 : σ →₀ ℕ)),
        (p.1 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g)) =
      ∑ p ∈ (Finset.antidiagonal (d + (Finsupp.single s 1 : σ →₀ ℕ))).filter
            (fun p ↦ (Finsupp.single s 1 : σ →₀ ℕ) ≤ p.1),
        (p.1 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g) := by
  symm
  apply Finset.sum_filter_of_ne
  intro p _ hne
  by_contra hle
  exact hne (smul_eq_zero_of_not_le hle _)

/-- Reindexing for the left half of the Leibniz rule: shifting the first
coordinate by `single s 1` is a bijection from the antidiagonal of `d` onto the
terms of the antidiagonal of `d + single s 1` with `single s 1 ≤ p.1`, and it
turns the scalar `p.1 s + 1` into `(p.1 + single s 1) s`. -/
private theorem sum_antidiagonal_shift_fst [DecidableEq σ] (s : σ)
    (f g : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    (∑ p ∈ Finset.antidiagonal d,
        (p.1 s + 1 : ℕ) •
          (coeff (R := R) (p.1 + Finsupp.single s 1) f * coeff (R := R) p.2 g)) =
      ∑ p ∈ (Finset.antidiagonal (d + (Finsupp.single s 1 : σ →₀ ℕ))).filter
            (fun p ↦ (Finsupp.single s 1 : σ →₀ ℕ) ≤ p.1),
        (p.1 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g) := by
  set e : σ →₀ ℕ := Finsupp.single s 1 with he
  -- Reindex using the explicit bijection. Use `sum_nbij'` with
  -- source = antidiag d, target = filter.
  refine Finset.sum_nbij' (fun p ↦ (p.1 + e, p.2)) (fun p ↦ (p.1 - e, p.2))
    ?_ ?_ ?_ ?_ ?_
  · -- forward `(p.1 + e, p.2) ∈ filter` given `p ∈ antidiag d`
    intro p hp
    simp only [Finset.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal]
    refine ⟨?_, le_add_self⟩
    rw [add_right_comm, hp]
  · -- backward `(p.1 - e, p.2) ∈ antidiag d` given `p ∈ filter`
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    simp only [Finset.mem_antidiagonal]
    obtain ⟨hsum, hle⟩ := hp
    rw [tsub_add_eq_add_tsub hle, hsum]
    exact add_tsub_cancel_right _ _
  · -- left-inverse on antidiag d: (p + e) - e = p
    intro p _
    ext : 1
    · exact add_tsub_cancel_right _ _
    · rfl
  · -- right-inverse on filter: (p - e) + e = p
    intro p hp
    simp only [Finset.mem_filter] at hp
    ext : 1
    · exact tsub_add_cancel_of_le hp.2
    · rfl
  · -- value equality: `(p s + 1) • ... = (p + e) s • ...`.
    intro p hp
    simp only [Finset.mem_antidiagonal] at hp
    congr 1
    rw [Finsupp.add_apply, single_self_apply]

/-- Helper: the "left half" of the Leibniz rule expressed as a sum over
the antidiagonal of `d + single s 1`. -/
private theorem coeff_pderiv_mul_left [DecidableEq σ] (s : σ) (f g : MvPowerSeries σ R)
    (d : σ →₀ ℕ) :
    coeff (R := R) d (pderiv s f * g) =
      ∑ p ∈ Finset.antidiagonal (d + (Finsupp.single s 1 : σ →₀ ℕ)),
        (p.1 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g) := by
  -- Step 1: expand `coeff_mul` and `coeff_pderiv`, distribute the scalar.
  have hmul : coeff (R := R) d (pderiv s f * g) =
      ∑ p ∈ Finset.antidiagonal d,
        (p.1 s + 1 : ℕ) •
          (coeff (R := R) (p.1 + Finsupp.single s 1) f * coeff (R := R) p.2 g) := by
    rw [coeff_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [coeff_pderiv, smul_mul_assoc]
  -- Step 2: collapse the right-hand sum to the `single s 1 ≤ p.1` filter (the
  -- summand vanishes elsewhere), then reindex via `(p, q) ↦ (p + single s 1, q)`.
  rw [hmul, sum_antidiagonal_smul_fst_eq_filter s f g d, sum_antidiagonal_shift_fst s f g d]

/-- Helper: the "right half" of the Leibniz rule. -/
private theorem coeff_pderiv_mul_right [DecidableEq σ] (s : σ) (f g : MvPowerSeries σ R)
    (d : σ →₀ ℕ) :
    coeff (R := R) d (f * pderiv s g) =
      ∑ p ∈ Finset.antidiagonal (d + (Finsupp.single s 1 : σ →₀ ℕ)),
        (p.2 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g) := by
  set e : σ →₀ ℕ := Finsupp.single s 1 with he
  have hmul : coeff (R := R) d (f * pderiv s g) =
      ∑ p ∈ Finset.antidiagonal d,
        (p.2 s + 1 : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) (p.2 + e) g) := by
    rw [coeff_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [coeff_pderiv, mul_smul_comm]
  rw [hmul]
  rw [show (∑ p ∈ Finset.antidiagonal (d + e),
        (p.2 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g)) =
      ∑ p ∈ (Finset.antidiagonal (d + e)).filter (fun p ↦ e ≤ p.2),
        (p.2 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g) from ?_]
  · refine Finset.sum_nbij' (fun p ↦ (p.1, p.2 + e)) (fun p ↦ (p.1, p.2 - e))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_antidiagonal] at hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal]
      refine ⟨?_, le_add_self⟩
      rw [← add_assoc, hp]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
      simp only [Finset.mem_antidiagonal]
      obtain ⟨hsum, hle⟩ := hp
      rw [← add_tsub_assoc_of_le hle, hsum]
      exact add_tsub_cancel_right _ _
    · intro p _
      ext : 1
      · rfl
      · exact add_tsub_cancel_right _ _
    · intro p hp
      simp only [Finset.mem_filter] at hp
      ext : 1
      · rfl
      · exact tsub_add_cancel_of_le hp.2
    · intro p hp
      simp only [Finset.mem_antidiagonal] at hp
      congr 1
      rw [Finsupp.add_apply, single_self_apply]
  · symm
    apply Finset.sum_filter_of_ne
    intro p _ hne
    by_contra hle
    exact hne (smul_eq_zero_of_not_le hle _)

/-- **Leibniz rule** for the partial derivative on multivariate formal
power series. -/
theorem pderiv_mul (s : σ) (f g : MvPowerSeries σ R) :
    pderiv s (f * g) = pderiv s f * g + f * pderiv s g := by
  classical
  ext d
  have he_s : (Finsupp.single s 1 : σ →₀ ℕ) s = 1 := single_self_apply s
  -- LHS: `(d s + 1) • ∑_T coeff p f * coeff q g`, rewritten so each summand
  -- has scalar `(p.1 s + p.2 s)` (equal to `d s + 1` on the support).
  have hLHS : coeff (R := R) d (pderiv s (f * g)) =
      ∑ p ∈ Finset.antidiagonal (d + (Finsupp.single s 1 : σ →₀ ℕ)),
        (p.1 s + p.2 s : ℕ) • (coeff (R := R) p.1 f * coeff (R := R) p.2 g) := by
    rw [coeff_pderiv, coeff_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_antidiagonal] at hp
    congr 1
    have hds : (p.1 + p.2) s = (d + (Finsupp.single s 1 : σ →₀ ℕ)) s := by rw [hp]
    simp only [Finsupp.add_apply, he_s] at hds
    omega
  rw [hLHS, map_add, coeff_pderiv_mul_left s f g d, coeff_pderiv_mul_right s f g d,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [add_smul]

/-! ### Monomial formula -/

/-- Per-coefficient identity behind `pderiv_monomial` when `single s 1 ≤ n`: the `coeff d` of
`pderiv s (monomial n a)`, namely `(d s + 1) • coeff_{d + single s 1} (monomial n a)`, equals
`coeff d (monomial (n - single s 1) (a * n s))`. On the diagonal `d + single s 1 = n` we have
`d s + 1 = n s`, turning `(d s + 1) • a` into `a * n s`; off the diagonal both sides vanish
(`d + single s 1 = n ↔ d = n - single s 1` since `single s 1 ≤ n`). -/
private lemma coeff_pderiv_monomial_single_le {s : σ} {n d : σ →₀ ℕ} {a : R}
    (hle : Finsupp.single s 1 ≤ n) :
    (d s + 1 : ℕ) • coeff (R := R) (d + Finsupp.single s 1) (monomial n a) =
      coeff (R := R) d (monomial (n - Finsupp.single s 1) (a * n s)) := by
  classical
  have he_s : (Finsupp.single s 1 : σ →₀ ℕ) s = 1 := single_self_apply s
  rw [coeff_monomial, coeff_monomial]
  by_cases hd : d + Finsupp.single s 1 = n
  · -- d = n - single s 1; hence d s + 1 = n s.
    have hdeq : d = n - Finsupp.single s 1 := by
      rw [← hd]
      exact (add_tsub_cancel_right d _).symm
    rw [if_pos hd, if_pos hdeq]
    -- `(d s + 1) • a = a * n s`.
    have heq : d s + 1 = n s := by
      have hds : (d + Finsupp.single s 1 : σ →₀ ℕ) s = n s := by rw [hd]
      simp only [Finsupp.add_apply, he_s] at hds
      exact hds
    rw [heq, nsmul_eq_mul, mul_comm]
  · rw [if_neg hd]
    -- d + single s 1 ≠ n means d ≠ n - single s 1 (when single s 1 ≤ n).
    have hd' : d ≠ n - Finsupp.single s 1 := by
      intro heq
      apply hd
      rw [heq, tsub_add_cancel_of_le hle]
    rw [if_neg hd', smul_zero]

/-- Per-coefficient identity behind `pderiv_monomial` when `¬ single s 1 ≤ n` (i.e.
`single s 1 ⊄ n`): then `n s = 0`, so the right-hand coefficient `a * n s` vanishes, and
`d + single s 1 = n` can never hold, so the left-hand coefficient vanishes too. -/
private lemma coeff_pderiv_monomial_not_single_le {s : σ} {n d : σ →₀ ℕ} {a : R}
    (hle : ¬ Finsupp.single s 1 ≤ n) :
    (d s + 1 : ℕ) • coeff (R := R) (d + Finsupp.single s 1) (monomial n a) =
      coeff (R := R) d (monomial (n - Finsupp.single s 1) (a * n s)) := by
  classical
  have he_s : (Finsupp.single s 1 : σ →₀ ℕ) s = 1 := single_self_apply s
  rw [coeff_monomial, coeff_monomial]
  -- `single s 1 ⊄ n` forces `n s = 0`.
  have hns : n s = 0 := by
    by_contra hne
    apply hle
    intro i
    by_cases hi : i = s
    · subst hi
      rw [he_s]
      exact Nat.one_le_iff_ne_zero.mpr hne
    · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      exact Nat.zero_le _
  rw [hns, Nat.cast_zero, mul_zero]
  -- and `d + single s 1 = n` is impossible.
  have hne : d + Finsupp.single s 1 ≠ n := by
    intro heq
    apply hle
    rw [← heq]
    exact le_add_self
  rw [if_neg hne, smul_zero]
  split_ifs <;> rfl

theorem pderiv_monomial (s : σ) (n : σ →₀ ℕ) (a : R) :
    pderiv s (monomial n a) = monomial (n - Finsupp.single s 1) (a * n s) := by
  ext d
  rw [coeff_pderiv]
  by_cases hle : Finsupp.single s 1 ≤ n
  · exact coeff_pderiv_monomial_single_le hle
  · exact coeff_pderiv_monomial_not_single_le hle

end CommSemiring

/-! ### Subtraction and negation (need `Ring`) -/

section CommRing

variable [CommRing R]

theorem pderiv_neg (s : σ) (f : MvPowerSeries σ R) : pderiv s (-f) = -pderiv s f := by
  ext d
  simp [coeff_pderiv]

theorem pderiv_sub (s : σ) (f g : MvPowerSeries σ R) :
    pderiv s (f - g) = pderiv s f - pderiv s g := by
  ext d
  simp [coeff_pderiv, map_sub, smul_sub]

end CommRing

/-! ### Agreement with `MvPolynomial.pderiv` -/

section CommSemiring

variable [CommSemiring R]

theorem pderiv_coe (s : σ) (p : MvPolynomial σ R) :
    MvPowerSeries.pderiv s (p : MvPowerSeries σ R) =
      ((MvPolynomial.pderiv s p : MvPolynomial σ R) : MvPowerSeries σ R) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial n a =>
    rw [MvPolynomial.coe_monomial, pderiv_monomial, MvPolynomial.pderiv_monomial,
        MvPolynomial.coe_monomial]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, pderiv_add, hp, hq, map_add, MvPolynomial.coe_add]

end CommSemiring

/-! ### Continuity of `pderiv` in the Pi topology -/

section Continuity

variable [CommSemiring R] [TopologicalSpace R] [ContinuousConstSMul ℕ R]

open scoped MvPowerSeries.WithPiTopology

/-- The formal partial derivative `pderiv s` is continuous in the product topology
on `MvPowerSeries σ R`. -/
theorem continuous_pderiv (s : σ) :
    Continuous (MvPowerSeries.pderiv (R := R) (σ := σ) s) := by
  classical
  refine continuous_pi_iff.mpr fun d ↦ ?_
  -- `coeff d (pderiv s f) = (d s + 1) • coeff (d + single s 1) f`
  have heq : (fun f : MvPowerSeries σ R ↦
      (MvPowerSeries.pderiv s f) d) =
      fun f : MvPowerSeries σ R ↦
        (d s + 1 : ℕ) • coeff (R := R) (d + Finsupp.single s 1) f := by
    funext f
    change coeff (R := R) d (MvPowerSeries.pderiv s f) = _
    rw [coeff_pderiv]
  rw [heq]
  exact (WithPiTopology.continuous_coeff R
    (d + Finsupp.single s 1)).const_smul _

end Continuity

/-! ### Substitution chain rule -/

section Subst

variable [CommRing R]
variable {τ : Type*}

open scoped MvPowerSeries.WithPiTopology

/-- The polynomial case of the general substitution chain rule: for every
`p : MvPolynomial σ R` (with `σ` finite) and every target variable `t : τ`,
`pderiv t (subst a p) = ∑ s, pderiv t (a s) * subst a (pderiv s p)`
(viewing `p` as a power series). This is the finitary form (Finset sum). -/
private theorem pderiv_subst_polynomial {σ : Type*} [Fintype σ]
    (t : τ) {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (p : MvPolynomial σ R) :
    MvPowerSeries.pderiv t
        (MvPowerSeries.subst a (p : MvPowerSeries σ R)) =
      ∑ s : σ, MvPowerSeries.pderiv t (a s) *
          MvPowerSeries.subst a (MvPowerSeries.pderiv s (p : MvPowerSeries σ R)) := by
  classical
  have hsubst0 : MvPowerSeries.subst a (0 : MvPowerSeries σ R) = 0 := by
    rw [← MvPowerSeries.substAlgHom_apply ha, map_zero]
  have hsubst1 : MvPowerSeries.subst a (1 : MvPowerSeries σ R) = 1 := by
    rw [← MvPowerSeries.substAlgHom_apply ha, map_one]
  induction p using MvPolynomial.induction_on with
  | C r =>
    -- `pderiv t (subst a (C r)) = 0`, and RHS is also 0.
    rw [MvPolynomial.coe_C]
    have hCr : (C r : MvPowerSeries σ R) =
        algebraMap R (MvPowerSeries σ R) r := rfl
    rw [hCr]
    have hsubst : MvPowerSeries.subst a
        (algebraMap R (MvPowerSeries σ R) r) =
          algebraMap R (MvPowerSeries τ R) r := by
      have := MvPowerSeries.substAlgHom_apply (R := R) ha
        (algebraMap R (MvPowerSeries σ R) r)
      rw [← this, AlgHom.commutes]
    rw [hsubst]
    have halg : algebraMap R (MvPowerSeries τ R) r = (C r : MvPowerSeries τ R) := rfl
    have halg₂ : algebraMap R (MvPowerSeries σ R) r =
        (C r : MvPowerSeries σ R) := rfl
    rw [halg, halg₂, pderiv_C]
    -- RHS: for each `s`, `pderiv s (C r) = 0`, so `subst a 0 = 0`.
    symm
    apply Finset.sum_eq_zero
    intro s _
    rw [pderiv_C, hsubst0, mul_zero]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, MvPowerSeries.subst_add ha, pderiv_add]
    rw [hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [pderiv_add, MvPowerSeries.subst_add ha, mul_add]
  | mul_X p i h =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X,
        MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, pderiv_mul]
    rw [h]
    -- Transform RHS summand-by-summand.
    have hsubst_X_pderiv : ∀ s : σ,
        MvPowerSeries.subst a (MvPowerSeries.pderiv s (X i : MvPowerSeries σ R)) =
          if s = i then 1 else 0 := by
      intro s
      split_ifs with hs
      · subst hs
        rw [pderiv_X_self, hsubst1]
      · rw [pderiv_X_of_ne hs, hsubst0]
    have hsummand : ∀ s : σ, MvPowerSeries.pderiv t (a s) *
          MvPowerSeries.subst a
            (MvPowerSeries.pderiv s
              ((p : MvPowerSeries σ R) * (X i : MvPowerSeries σ R))) =
        MvPowerSeries.pderiv t (a s) *
          MvPowerSeries.subst a (MvPowerSeries.pderiv s
              (p : MvPowerSeries σ R)) * a i +
        MvPowerSeries.pderiv t (a s) *
          MvPowerSeries.subst a (p : MvPowerSeries σ R) *
          (if s = i then 1 else 0) := by
      intro s
      rw [pderiv_mul, MvPowerSeries.subst_add ha,
          MvPowerSeries.subst_mul ha, MvPowerSeries.subst_mul ha,
          MvPowerSeries.subst_X ha]
      rw [hsubst_X_pderiv s]
      ring
    -- Rewrite both sides in canonical form.
    conv_rhs =>
      rw [show (∑ s : σ, MvPowerSeries.pderiv t (a s) *
          MvPowerSeries.subst a
            (MvPowerSeries.pderiv s
              ((p : MvPowerSeries σ R) * (X i : MvPowerSeries σ R)))) =
          ∑ s : σ, (MvPowerSeries.pderiv t (a s) *
            MvPowerSeries.subst a (MvPowerSeries.pderiv s
              (p : MvPowerSeries σ R)) * a i +
          MvPowerSeries.pderiv t (a s) *
            MvPowerSeries.subst a (p : MvPowerSeries σ R) *
            (if s = i then 1 else 0)) from
          Finset.sum_congr rfl fun s _ ↦ hsummand s]
    rw [Finset.sum_add_distrib]
    congr 1
    · -- `(∑ s, f s) * a i = ∑ s, f s * a i`
      exact Finset.sum_mul ..
    · -- Second sum picks out `s = i`, giving `subst a p * pderiv t (a i)`.
      rw [Finset.sum_eq_single i
        (fun b _ hb ↦ by simp [hb])
        (fun hi ↦ (hi (Finset.mem_univ i)).elim)]
      simp [mul_comm]

/-- **Substitution chain rule for `MvPowerSeries.pderiv`** for a finite index
type `σ`. For `f : MvPowerSeries σ R`, a family `a : σ → MvPowerSeries τ R`
with `HasSubst a`, and a target variable `t : τ`:

`pderiv t (subst a f) = ∑ s : σ, pderiv t (a s) * subst a (pderiv s f)`. -/
theorem pderiv_subst {σ : Type*} [Fintype σ]
    (t : τ) {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.pderiv t (MvPowerSeries.subst a f) =
      ∑ s : σ, MvPowerSeries.pderiv t (a s) *
        MvPowerSeries.subst a (MvPowerSeries.pderiv s f) := by
  classical
  letI : UniformSpace R := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  -- Both sides as continuous functions of `f`.
  let LHS : MvPowerSeries σ R → MvPowerSeries τ R :=
    fun f ↦ MvPowerSeries.pderiv t (MvPowerSeries.subst a f)
  let RHS : MvPowerSeries σ R → MvPowerSeries τ R :=
    fun f ↦ ∑ s : σ, MvPowerSeries.pderiv t (a s) *
      MvPowerSeries.subst a (MvPowerSeries.pderiv s f)
  -- Continuity of LHS.
  have hLHS_cont : Continuous LHS :=
    (continuous_pderiv t).comp (continuous_subst ha)
  -- Continuity of RHS.
  have hRHS_cont : Continuous RHS := by
    apply continuous_finsetSum
    intro s _
    exact continuous_const.mul ((continuous_subst ha).comp (continuous_pderiv s))
  -- The two functions agree on polynomial inputs.
  have hpoly : ∀ p : MvPolynomial σ R,
      LHS (p : MvPowerSeries σ R) = RHS (p : MvPowerSeries σ R) :=
    fun p ↦ pderiv_subst_polynomial t ha p
  -- Polynomials are dense in power series (pi topology).
  have hdense : DenseRange
      (MvPolynomial.toMvPowerSeries (R := R) (σ := σ)) :=
    WithPiTopology.denseRange_toMvPowerSeries
  -- Extend by continuity.
  have heq : LHS = RHS := by
    apply Continuous.ext_on hdense hLHS_cont hRHS_cont
    rintro _ ⟨p, rfl⟩
    exact hpoly p
  exact congrFun heq f

/-- **Substitution chain rule for `MvPowerSeries.pderiv`** specialized to
`σ = Fin 2`. For `f : MvPowerSeries (Fin 2) R`, a family `a : Fin 2 →
MvPowerSeries τ R` with `HasSubst a`, and a target variable `t : τ`:

`pderiv t (subst a f) = pderiv t (a 0) * subst a (pderiv 0 f)
                         + pderiv t (a 1) * subst a (pderiv 1 f)`.

This is the form used in Silverman IV.4.2 (translation invariance of the
invariant differential on a formal group). -/
theorem pderiv_subst_fin2
    (t : τ) {a : Fin 2 → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.pderiv t (MvPowerSeries.subst a f) =
      MvPowerSeries.pderiv t (a 0) * MvPowerSeries.subst a (MvPowerSeries.pderiv 0 f) +
      MvPowerSeries.pderiv t (a 1) * MvPowerSeries.subst a (MvPowerSeries.pderiv 1 f) := by
  rw [pderiv_subst t ha f, Fin.sum_univ_two]

end Subst

end MvPowerSeries

end

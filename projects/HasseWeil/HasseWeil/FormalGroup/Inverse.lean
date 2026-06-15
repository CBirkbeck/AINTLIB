import HasseWeil.FormalGroup.Definition
import HasseWeil.FormalGroup.Logarithm

/-!
# The formal inverse of a formal group (Silverman IV.2)

For a formal group law `F(X, Y) ∈ R[[X, Y]]`, this file constructs the
**formal inverse** power series `i(T) ∈ R[[T]]` characterised by

`F(T, i(T)) = 0`,       `constantCoeff i = 0`.

The existence of `i(T)` is a consequence of the unit axioms on `F` together
with a routine coefficient-by-coefficient recursion: writing
`F(X, Y) = X + Y + (higher order)`, the relation `F(T, i(T)) = 0` forces
`coeff 1 i = -1` and then determines `coeff n i` for `n ≥ 2` from the
previously-computed coefficients.

## Main definitions

* `HasseWeil.FormalGroup.FormalGroup.inverseTrunc F n` — the degree-`n`
  truncation (as a power series) of the formal inverse.
* `HasseWeil.FormalGroup.FormalGroup.inverseCoeff F n` — the coefficient at
  `T^n` of the formal inverse, stabilised from the truncation.
* `HasseWeil.FormalGroup.FormalGroup.inverse F` — the formal inverse power
  series `i(T)`.

## Main results

* `FormalGroup.inverse_constantCoeff` — `constantCoeff i = 0`.
* `FormalGroup.inverse_coeff_zero` — `coeff 0 i = 0`.
* `FormalGroup.inverse_coeff_one` — `coeff 1 i = -1`.

The functional equation `F(T, i(T)) = 0` (to be theorem
`FormalGroup.fAdd_X_inverse_eq_zero`) is deferred to a follow-up ticket
(T-IV-2-011 remainder); its proof closely mirrors
`subst_compInverse_eq_X` in `HasseWeil/FormalGroup/Logarithm.lean` but for
the two-variable implicit equation.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.2.
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-! ### Iterative construction of the formal inverse

We mirror the pattern of `compInvTrunc` / `compInvCoeff` / `compInverse` in
`HasseWeil/FormalGroup/Logarithm.lean`, but for the two-variable fixed-point
equation `F(T, i(T)) = 0`.

At each step `n + 1`, we add a correction `c · T^(n+1)` to the previous
truncation. The correction is `c = -coeff (n+1) (fAdd F X prev)`: adding
`c · T^(n+1)` to `prev` changes the coefficient of `fAdd F X prev` at
`T^(n+1)` by `c` (to leading order, because the coefficient of `Y` in
`F(X, Y)` is `1`), so taking `c` to be `-(coeff (n+1) current)` zeroes out
the `(n+1)`-th coefficient of `fAdd F X iterTrunc`. -/

/-- Iterative truncation of the formal inverse of `F`. -/
noncomputable def FormalGroup.inverseTrunc (F : FormalGroup R) :
    ℕ → PowerSeries R
  | 0 => 0
  | n + 1 =>
    let prev := inverseTrunc F n
    let current := HasseWeil.FG.fAdd F PowerSeries.X prev
    prev + PowerSeries.C (-PowerSeries.coeff (n + 1) current) *
              PowerSeries.X ^ (n + 1)

/-- The `n`-th coefficient of the formal inverse of `F`. -/
noncomputable def FormalGroup.inverseCoeff (F : FormalGroup R) (n : ℕ) : R :=
  PowerSeries.coeff n (F.inverseTrunc n)

/-- The **formal inverse** of a formal group `F`.

This is the unique power series `i(T) ∈ R[[T]]` with `constantCoeff i = 0`
satisfying `F(T, i(T)) = 0`. Defined coefficient-by-coefficient via
`inverseCoeff`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2. -/
noncomputable def FormalGroup.inverse (F : FormalGroup R) : PowerSeries R :=
  PowerSeries.mk F.inverseCoeff

/-! ### Basic coefficient lemmas -/

@[simp]
theorem FormalGroup.inverseTrunc_zero (F : FormalGroup R) :
    F.inverseTrunc 0 = 0 :=
  rfl

@[simp]
theorem FormalGroup.inverseCoeff_zero (F : FormalGroup R) :
    F.inverseCoeff 0 = 0 := by
  simp [FormalGroup.inverseCoeff]

/-- The `0`-th coefficient of `inverse F` is zero. -/
@[simp]
theorem FormalGroup.inverse_coeff_zero (F : FormalGroup R) :
    PowerSeries.coeff 0 F.inverse = 0 := by
  simp [FormalGroup.inverse]

/-- The constant coefficient of `inverse F` is zero. -/
@[simp]
theorem FormalGroup.inverse_constantCoeff (F : FormalGroup R) :
    @PowerSeries.constantCoeff R _ F.inverse = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact F.inverse_coeff_zero

/-! ### Structural lemmas mirroring `compInvTrunc`

These establish that `inverseTrunc` is a "polynomial tail" — adding the
degree-`(n+1)` correction does not change lower coefficients — and that
`inverseTrunc F n` has zero constant coefficient. -/

/-- `inverseTrunc F (n+1)` differs from `inverseTrunc F n` only by a monomial
of degree `n+1`; in particular, its lower coefficients coincide. -/
theorem FormalGroup.coeff_inverseTrunc_succ_of_le (F : FormalGroup R)
    (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k (F.inverseTrunc (n + 1)) =
      PowerSeries.coeff k (F.inverseTrunc n) := by
  -- Unfold the recursive definition.
  change PowerSeries.coeff k
      (F.inverseTrunc n +
        PowerSeries.C _ * PowerSeries.X ^ (n + 1)) = _
  rw [map_add, PowerSeries.coeff_C_mul_X_pow]
  -- `k ≠ n + 1` since `k ≤ n`.
  rw [if_neg (by omega : k ≠ n + 1), add_zero]

/-- For `k ≤ n`, the `k`-th coefficient of `inverseTrunc F n` equals the
stable coefficient `inverseCoeff F k`. -/
theorem FormalGroup.coeff_inverseTrunc_of_le (F : FormalGroup R)
    (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k (F.inverseTrunc n) = F.inverseCoeff k := by
  induction n with
  | zero =>
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    simp [FormalGroup.inverseCoeff]
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hk'' : k ≤ n := Nat.lt_succ_iff.mp hk'
      rw [F.coeff_inverseTrunc_succ_of_le n k hk'']
      exact ih hk''
    · -- `k = n + 1`, direct from definition of `inverseCoeff`.
      have : k = n + 1 := le_antisymm hk hk'
      subst this
      rfl

/-- `inverseTrunc F n` has zero constant coefficient. -/
theorem FormalGroup.inverseTrunc_constantCoeff (F : FormalGroup R) (n : ℕ) :
    @PowerSeries.constantCoeff R _ (F.inverseTrunc n) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [F.coeff_inverseTrunc_of_le n 0 (Nat.zero_le _)]
  exact F.inverseCoeff_zero

/-- `inverseTrunc F n` admits substitution (zero constant coefficient). -/
theorem FormalGroup.inverseTrunc_hasSubst (F : FormalGroup R) (n : ℕ) :
    PowerSeries.HasSubst (F.inverseTrunc n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (F.inverseTrunc_constantCoeff n)

/-- `inverse F` admits substitution. -/
theorem FormalGroup.inverse_hasSubst (F : FormalGroup R) :
    PowerSeries.HasSubst F.inverse :=
  PowerSeries.HasSubst.of_constantCoeff_zero' F.inverse_constantCoeff

/-! ### Computation of the linear coefficient

We compute `coeff 1 (inverse F) = -1`. This follows from unfolding the
definition of `inverseTrunc F 1` and using `coeff_one_fAdd`. -/

/-- The linear coefficient of `inverse F` is `-1`. -/
@[simp]
theorem FormalGroup.inverse_coeff_one (F : FormalGroup R) :
    PowerSeries.coeff 1 F.inverse = -1 := by
  -- `coeff 1 inverse = inverseCoeff 1` (by definition of `inverse` via `mk`).
  have h_unfold : PowerSeries.coeff 1 F.inverse = F.inverseCoeff 1 := by
    simp [FormalGroup.inverse]
  rw [h_unfold]
  -- `inverseCoeff 1 = coeff 1 (inverseTrunc F 1)` by definition.
  change PowerSeries.coeff 1 (F.inverseTrunc 1) = -1
  -- Unfold `inverseTrunc F 1 = 0 + C (-coeff 1 (fAdd F X 0)) * X^1`.
  change PowerSeries.coeff 1
      (F.inverseTrunc 0 +
        PowerSeries.C (-PowerSeries.coeff 1
          (HasseWeil.FG.fAdd F PowerSeries.X (F.inverseTrunc 0))) *
        PowerSeries.X ^ (0 + 1)) = -1
  rw [map_add, FormalGroup.inverseTrunc_zero, map_zero, zero_add]
  -- Simplify the coefficient expression.
  rw [PowerSeries.coeff_C_mul_X_pow]
  rw [if_pos (by norm_num : (1 : ℕ) = 0 + 1)]
  -- Goal: `-coeff 1 (fAdd F X 0) = -1`, i.e., `coeff 1 (fAdd F X 0) = 1`.
  have hX : @PowerSeries.constantCoeff R _ PowerSeries.X = 0 := by simp
  have hzero : @PowerSeries.constantCoeff R _ (0 : PowerSeries R) = 0 := by simp
  rw [HasseWeil.FG.coeff_one_fAdd F PowerSeries.X (0 : PowerSeries R) hX hzero]
  simp

/-! ### Functional equation `F(T, i(T)) = 0`

Closing T-IV-2-011: we show `fAdd F X (inverse F) = 0` by the pattern
"polynomial tail / substitution stabilisation / induction on truncations"
mirroring `subst_compInverse_eq_X` in `Logarithm.lean`. The new ingredient
is the MvPowerSeries analogue of the stabilisation step: because
`fAdd F X g = MvPowerSeries.subst ![X, g] F.toSeries`, we need to show that
the substitution's coefficient at degree `k` is unchanged by modifying `g`
in degrees `> n ≥ k`.
-/

open PowerSeries

section InversionProof

variable {R : Type*} [CommRing R]

/-- Coefficient stabilisation for `PowerSeries.coeff k (X^a * g^b)`: if `g₁`
and `g₂` agree up to degree `n`, then `coeff k (X^a * g₁^b) = coeff k (X^a * g₂^b)`
for every `k ≤ n`, provided both series have zero constant coefficient. -/
private theorem coeff_X_pow_mul_pow_eq_of_coeff_eq
    (g₁ g₂ : PowerSeries R)
    (h1 : @PowerSeries.constantCoeff R _ g₁ = 0)
    (h2 : @PowerSeries.constantCoeff R _ g₂ = 0)
    (n : ℕ) (hg : ∀ j ≤ n, PowerSeries.coeff j g₁ = PowerSeries.coeff j g₂)
    (a b k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k ((PowerSeries.X : PowerSeries R) ^ a * g₁ ^ b) =
      PowerSeries.coeff k ((PowerSeries.X : PowerSeries R) ^ a * g₂ ^ b) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  have hij' : i + j = k := Finset.mem_antidiagonal.mp hij
  -- Simplify X^a coefficient.
  show PowerSeries.coeff i ((PowerSeries.X : PowerSeries R) ^ a) *
        PowerSeries.coeff j (g₁ ^ b) =
      PowerSeries.coeff i ((PowerSeries.X : PowerSeries R) ^ a) *
        PowerSeries.coeff j (g₂ ^ b)
  -- Either i = a (then the X-factor gives 1) or i ≠ a (gives 0).
  by_cases hia : i = a
  · subst hia
    have hj_le : j ≤ n := by omega
    by_cases hjb : j ≥ b
    · congr 1
      exact coeff_pow_eq_of_coeff_eq g₁ g₂ n hg b j hj_le
    · push_neg at hjb
      have e1 : PowerSeries.coeff j (g₁ ^ b) = 0 := coeff_pow_eq_zero_of_gt g₁ h1 j b hjb
      have e2 : PowerSeries.coeff j (g₂ ^ b) = 0 := coeff_pow_eq_zero_of_gt g₂ h2 j b hjb
      rw [e1, e2]
  · rw [PowerSeries.coeff_X_pow, if_neg (fun h => hia h)]
    rw [zero_mul, zero_mul]

/-- **MvPowerSeries stabilisation for the `![X, g]` substitution**: if `g₁` and
`g₂` have zero constant coefficient and agree up to degree `n`, then
`fAdd F X g₁` and `fAdd F X g₂` agree up to degree `n`. -/
theorem FormalGroup.coeff_fAdd_X_eq_of_coeff_eq
    (F : FormalGroup R) (g₁ g₂ : PowerSeries R)
    (h1 : @PowerSeries.constantCoeff R _ g₁ = 0)
    (h2 : @PowerSeries.constantCoeff R _ g₂ = 0)
    (n : ℕ) (hg : ∀ j ≤ n, PowerSeries.coeff j g₁ = PowerSeries.coeff j g₂)
    (k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k (HasseWeil.FG.fAdd F PowerSeries.X g₁) =
      PowerSeries.coeff k (HasseWeil.FG.fAdd F PowerSeries.X g₂) := by
  have hXcc : @PowerSeries.constantCoeff R _ PowerSeries.X = 0 := by simp
  -- General helper: we prove the main coefficient formula for any particular
  -- g with zero constant coefficient.
  have main : ∀ (g : PowerSeries R), @PowerSeries.constantCoeff R _ g = 0 →
      PowerSeries.coeff k (HasseWeil.FG.fAdd F PowerSeries.X g) =
      ∑ᶠ (d : Fin 2 →₀ ℕ), MvPowerSeries.coeff d F.toSeries •
        PowerSeries.coeff k
          ((PowerSeries.X : PowerSeries R) ^ (d 0) * g ^ (d 1)) := by
    intro g hg0
    have ha := HasseWeil.FG.hasSubst_pair (PowerSeries.X : PowerSeries R) g hXcc hg0
    show MvPowerSeries.coeff (Finsupp.single () k)
        (MvPowerSeries.subst _ F.toSeries) = _
    rw [MvPowerSeries.coeff_subst ha]
    apply finsum_congr
    intro d
    congr 1
    -- Expand `d.prod (s e => ![X, g] s ^ e)` to `X^(d 0) * g^(d 1)`.
    rw [Finsupp.prod_fintype _ _ (fun i => by fin_cases i <;> exact pow_zero _),
        Fin.prod_univ_two]
    rfl
  rw [main g₁ h1, main g₂ h2]
  apply finsum_congr
  intro d
  congr 1
  exact coeff_X_pow_mul_pow_eq_of_coeff_eq g₁ g₂ h1 h2 n hg (d 0) (d 1) k hk

/-! ### Auxiliary computations for the monomial-addition lemma

The key insight: for `h = C c * X^(n+1)` (monomial of order `n+1`), coefficients
`coeff k` with `k < n+1` are not affected by replacing `g` with `g + h`, because
`h` has order `n+1`. This lets us reduce the `a ≥ 1` case by factoring out
`X^a` and shifting indices.
-/

/-- For `h = C c * X^(n+1)` and any `d`, the coefficient `coeff k ((g + h)^d)` at
`k < n+1` equals `coeff k (g^d)`. (Adding a high-order monomial doesn't affect
low-degree coefficients.) -/
private theorem coeff_add_monomial_pow_stable
    (g : PowerSeries R) (_hg : @PowerSeries.constantCoeff R _ g = 0)
    (n : ℕ) (c : R) (d : ℕ) (k : ℕ) (hk : k < n + 1) :
    PowerSeries.coeff k
        ((g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ d) =
      PowerSeries.coeff k (g ^ d) := by
  set h : PowerSeries R := PowerSeries.C c * PowerSeries.X ^ (n + 1) with hdef
  -- Use the commuted binomial: (h + g)^d = Σ h^m * g^(d-m) * choose(d,m).
  have hcomm : (h + g) ^ d =
      ∑ m ∈ Finset.range (d + 1), h ^ m * g ^ (d - m) * (d.choose m : PowerSeries R) :=
    add_pow h g d
  rw [show g + h = h + g from add_comm _ _, hcomm]
  rw [map_sum]
  -- Split sum: m = 0 term = h^0 * g^d * 1 = g^d; m ≥ 1 terms vanish at coeff k.
  rw [Finset.sum_eq_single 0]
  · -- Goal: coeff k (h^0 * g^(d-0) * (choose(d,0) : PS)) = coeff k (g^d).
    rw [pow_zero, Nat.sub_zero, Nat.choose_zero_right]
    -- Goal: coeff k (1 * g^d * ↑1) = coeff k (g^d).
    congr 1
    -- Goal: 1 * g ^ d * ↑1 = g ^ d.
    -- Try `simp` first since rewriting is finicky.
    push_cast
    -- After push_cast: 1 * g^d * 1 = g^d.
    exact (mul_one _).trans (one_mul _)
  · intro m _ hm0
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    -- Goal: coeff k (h^m * g^(d-m) * choose(d,m)) = 0.
    rw [hdef, monomial_pow_eq]
    -- h^m = C (c^m) * X^(m*(n+1)).
    have hnatCast : ((d.choose m : ℕ) : PowerSeries R) = PowerSeries.C ((d.choose m : ℕ) : R) := by
      induction (d.choose m) with
      | zero => push_cast; exact (map_zero _).symm
      | succ k ih =>
        rw [show ((k + 1 : ℕ) : PowerSeries R) = ((k : ℕ) : PowerSeries R) + 1 from by
              push_cast; rfl]
        rw [ih]
        rw [show ((k + 1 : ℕ) : R) = ((k : ℕ) : R) + 1 from by push_cast; rfl]
        rw [map_add, map_one]
    rw [hnatCast]
    -- Goal: coeff k (C (c^m) * X^(m*(n+1)) * g^(d-m) * C ↑choose) = 0
    -- Rearrange using explicit term-level rewriting via congruence.
    have reorg : PowerSeries.C (c ^ m) * PowerSeries.X ^ (m * (n + 1)) *
            g ^ (d - m) *
            PowerSeries.C ((d.choose m : ℕ) : R) =
          PowerSeries.C ((d.choose m : ℕ) : R) *
            (PowerSeries.C (c ^ m) *
              (PowerSeries.X ^ (m * (n + 1)) * g ^ (d - m))) := by
      -- First: (C (c^m) * X^N) * g^(d-m) = C (c^m) * (X^N * g^(d-m)).
      have step1 : PowerSeries.C (c ^ m) * PowerSeries.X ^ (m * (n + 1)) * g ^ (d - m) =
          PowerSeries.C (c ^ m) * (PowerSeries.X ^ (m * (n + 1)) * g ^ (d - m)) :=
        mul_assoc _ _ _
      -- Substitute in LHS and commute.
      calc PowerSeries.C (c ^ m) * PowerSeries.X ^ (m * (n + 1)) *
            g ^ (d - m) *
            PowerSeries.C ((d.choose m : ℕ) : R)
          = (PowerSeries.C (c ^ m) *
              (PowerSeries.X ^ (m * (n + 1)) * g ^ (d - m))) *
              PowerSeries.C ((d.choose m : ℕ) : R) := by
            exact congr_arg (· * PowerSeries.C ((d.choose m : ℕ) : R)) step1
        _ = PowerSeries.C ((d.choose m : ℕ) : R) *
            (PowerSeries.C (c ^ m) *
              (PowerSeries.X ^ (m * (n + 1)) * g ^ (d - m))) := mul_comm _ _
    rw [reorg]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    -- coeff k (X^(m*(n+1)) * g^(d-m)) = 0 since m*(n+1) ≥ n+1 > k.
    have horder_X : k < m * (n + 1) := by
      calc k < n + 1 := hk
        _ ≤ m * (n + 1) := Nat.le_mul_of_pos_left _ hm_pos
    have hxprod : PowerSeries.coeff k
        ((PowerSeries.X : PowerSeries R) ^ (m * (n + 1)) * g ^ (d - m)) = 0 := by
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro ⟨p, q⟩ hpq
      have hpq' : p + q = k := Finset.mem_antidiagonal.mp hpq
      rw [PowerSeries.coeff_X_pow]
      rw [if_neg (by omega : p ≠ m * (n + 1)), zero_mul]
    rw [hxprod, mul_zero, mul_zero]
  · intro h0
    simp at h0

/-- The `(n+1)`-th coefficient of `X^a * (g + h)^j` picks up the change only
when `(a, j) = (0, 1)`: the change is exactly `c`. -/
private theorem coeff_X_pow_mul_add_monomial_pow
    (g : PowerSeries R) (hg : @PowerSeries.constantCoeff R _ g = 0)
    (n : ℕ) (c : R) (a j : ℕ) :
    PowerSeries.coeff (n + 1)
        ((PowerSeries.X : PowerSeries R) ^ a *
          (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ j) =
      PowerSeries.coeff (n + 1)
        ((PowerSeries.X : PowerSeries R) ^ a * g ^ j) +
      (if a = 0 ∧ j = 1 then c else 0) := by
  -- Split into cases: a = 0 vs. a ≥ 1.
  by_cases ha0 : a = 0
  · subst ha0
    -- X^0 = 1, so the goal simplifies.
    have hshift : (if (0 : ℕ) = 0 ∧ j = 1 then c else 0) = (if j = 1 then c else 0) := by
      by_cases hj : j = 1
      · simp [hj]
      · simp [hj]
    rw [show ((PowerSeries.X : PowerSeries R) ^ (0 : ℕ) *
          (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ j :
            PowerSeries R) =
        (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ j from by
      rw [pow_zero]; exact one_mul _]
    rw [show ((PowerSeries.X : PowerSeries R) ^ (0 : ℕ) * g ^ j : PowerSeries R) =
        g ^ j from by rw [pow_zero]; exact one_mul _]
    rw [hshift]
    exact coeff_add_monomial_pow_eq g hg n c j
  · -- a ≥ 1: the "if" vanishes, and we need to show
    -- coeff (n+1) (X^a * (g+h)^j) = coeff (n+1) (X^a * g^j).
    have hand_fail : ¬ (a = 0 ∧ j = 1) := fun hand => ha0 hand.1
    rw [if_neg hand_fail]
    rw [add_zero]
    -- By coeff_mul, coeff (n+1) (X^a * f) = coeff (n+1 - a) f (when a ≤ n+1).
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨p, q⟩ hpq
    have hpq' : p + q = n + 1 := Finset.mem_antidiagonal.mp hpq
    -- Goal: coeff p (X^a) * coeff q ((g+h)^j) = coeff p (X^a) * coeff q (g^j).
    show PowerSeries.coeff p ((PowerSeries.X : PowerSeries R) ^ a) *
          PowerSeries.coeff q ((g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ j) =
        PowerSeries.coeff p ((PowerSeries.X : PowerSeries R) ^ a) *
          PowerSeries.coeff q (g ^ j)
    by_cases hpa : p = a
    · have hq : q < n + 1 := by
        have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
        omega
      rw [hpa]
      congr 1
      exact coeff_add_monomial_pow_stable g hg n c j q hq
    · rw [PowerSeries.coeff_X_pow, if_neg hpa, zero_mul, zero_mul]

/-- **Monomial-addition step**: for `g : PowerSeries R` with zero constant
coefficient and any `c ∈ R`,
`coeff (n+1) (fAdd F X (g + C c * X^(n+1))) = coeff (n+1) (fAdd F X g) + c`.

This is the two-variable analogue of `coeff_subst_add_monomial` from
`Logarithm.lean`. The "+ c" arises from the fact that the coefficient of `Y`
in `F(X, Y)` is `1` (second unit axiom, see `FormalGroup.coeff_01`). -/
theorem FormalGroup.coeff_fAdd_X_add_monomial (F : FormalGroup R)
    (g : PowerSeries R) (n : ℕ) (c : R)
    (hg : @PowerSeries.constantCoeff R _ g = 0) :
    PowerSeries.coeff (n + 1)
        (HasseWeil.FG.fAdd F PowerSeries.X
          (g + PowerSeries.C c * PowerSeries.X ^ (n + 1))) =
      PowerSeries.coeff (n + 1) (HasseWeil.FG.fAdd F PowerSeries.X g) + c := by
  have hXcc : @PowerSeries.constantCoeff R _ PowerSeries.X = 0 := by simp
  have hh_cc : @PowerSeries.constantCoeff R _
      (PowerSeries.C c * PowerSeries.X ^ (n + 1)) = 0 := monomial_constantCoeff_zero n c
  have hgh_cc : @PowerSeries.constantCoeff R _
      (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) = 0 := by simp [hg, hh_cc]
  -- Use the same `main` identity, then compare term-by-term.
  have ha_gh := HasseWeil.FG.hasSubst_pair (PowerSeries.X : PowerSeries R)
      (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) hXcc hgh_cc
  have ha_g := HasseWeil.FG.hasSubst_pair (PowerSeries.X : PowerSeries R) g hXcc hg
  -- Unfold both substitutions.
  have lhs_eq :
      PowerSeries.coeff (n + 1)
          (HasseWeil.FG.fAdd F PowerSeries.X
            (g + PowerSeries.C c * PowerSeries.X ^ (n + 1))) =
      ∑ᶠ (d : Fin 2 →₀ ℕ), MvPowerSeries.coeff d F.toSeries •
        PowerSeries.coeff (n + 1)
          ((PowerSeries.X : PowerSeries R) ^ (d 0) *
            (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ (d 1)) := by
    show MvPowerSeries.coeff (Finsupp.single () (n + 1))
      (MvPowerSeries.subst _ F.toSeries) = _
    rw [MvPowerSeries.coeff_subst ha_gh]
    apply finsum_congr
    intro d
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => by fin_cases i <;> exact pow_zero _),
        Fin.prod_univ_two]
    rfl
  have rhs_eq :
      PowerSeries.coeff (n + 1)
          (HasseWeil.FG.fAdd F PowerSeries.X g) =
      ∑ᶠ (d : Fin 2 →₀ ℕ), MvPowerSeries.coeff d F.toSeries •
        PowerSeries.coeff (n + 1)
          ((PowerSeries.X : PowerSeries R) ^ (d 0) * g ^ (d 1)) := by
    show MvPowerSeries.coeff (Finsupp.single () (n + 1))
      (MvPowerSeries.subst _ F.toSeries) = _
    rw [MvPowerSeries.coeff_subst ha_g]
    apply finsum_congr
    intro d
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => by fin_cases i <;> exact pow_zero _),
        Fin.prod_univ_two]
    rfl
  rw [lhs_eq, rhs_eq]
  -- Now use the coeff_X_pow_mul_add_monomial_pow lemma to rewrite each LHS term.
  have key : ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d F.toSeries •
        PowerSeries.coeff (n + 1)
          ((PowerSeries.X : PowerSeries R) ^ (d 0) *
            (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ (d 1)) =
      MvPowerSeries.coeff d F.toSeries •
        PowerSeries.coeff (n + 1)
          ((PowerSeries.X : PowerSeries R) ^ (d 0) * g ^ (d 1)) +
      MvPowerSeries.coeff d F.toSeries •
        (if d 0 = 0 ∧ d 1 = 1 then c else 0) := by
    intro d
    rw [coeff_X_pow_mul_add_monomial_pow g hg n c (d 0) (d 1), smul_add]
  rw [show (fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F.toSeries •
          PowerSeries.coeff (n + 1)
            ((PowerSeries.X : PowerSeries R) ^ (d 0) *
              (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ (d 1))) =
        (fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F.toSeries •
          PowerSeries.coeff (n + 1)
            ((PowerSeries.X : PowerSeries R) ^ (d 0) * g ^ (d 1)) +
            MvPowerSeries.coeff d F.toSeries •
              (if d 0 = 0 ∧ d 1 = 1 then c else 0)) from funext key]
  -- Split the finsum into two.
  have hfin1 : (fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F.toSeries •
        PowerSeries.coeff (n + 1)
          ((PowerSeries.X : PowerSeries R) ^ (d 0) * g ^ (d 1))).support.Finite := by
    -- The support is finite because of MvPowerSeries.coeff_subst_finite.
    have hfinite := MvPowerSeries.coeff_subst_finite ha_g F.toSeries (Finsupp.single () (n + 1))
    -- `hfinite` is `HasFiniteSupport` which unfolds to `.support.Finite`.
    -- We show our support equals the original support.
    have hfinite' : (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d F.toSeries •
        MvPowerSeries.coeff (Finsupp.single () (n + 1))
          (d.prod fun s e =>
            (show Fin 2 → MvPowerSeries Unit R from ![PowerSeries.X, g]) s ^ e)).support.Finite :=
      hfinite
    refine hfinite'.subset ?_
    intro d hd
    simp only [Function.mem_support] at hd ⊢
    -- hd : coeff d F • coeff (n+1) (X^(d 0) * g^(d 1)) ≠ 0.
    -- goal: coeff d F • coeff (Finsupp.single () (n+1)) (d.prod ...) ≠ 0.
    -- We show `d.prod ... = X^(d 0) * g^(d 1)` as MvPowerSeries Unit R elements,
    -- then the coeffs are equal.
    have prod_eq :
        (MvPowerSeries.coeff (Finsupp.single () (n + 1))
            (d.prod fun s e =>
              (show Fin 2 → MvPowerSeries Unit R from ![PowerSeries.X, g]) s ^ e)) =
          PowerSeries.coeff (n + 1)
            ((PowerSeries.X : PowerSeries R) ^ (d 0) * g ^ (d 1)) := by
      congr 1
      rw [Finsupp.prod_fintype _ _ (fun i => by fin_cases i <;> exact pow_zero _),
          Fin.prod_univ_two]
      rfl
    rw [prod_eq]
    exact hd
  have hfin2 : (fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F.toSeries •
        (if d 0 = 0 ∧ d 1 = 1 then c else 0)).support.Finite := by
    -- Support ⊆ {Finsupp.single 1 1}.
    apply Set.Finite.subset (Set.finite_singleton (Finsupp.single (1 : Fin 2) 1))
    intro d hd
    simp only [Function.mem_support] at hd
    -- Need: d = Finsupp.single 1 1.
    by_contra hne
    apply hd
    have : ¬ (d 0 = 0 ∧ d 1 = 1) := by
      intro ⟨h0, h1⟩
      apply hne
      ext i
      fin_cases i <;> simp [Finsupp.single_apply, h0, h1]
    rw [if_neg this, smul_zero]
  rw [finsum_add_distrib hfin1 hfin2]
  -- The second finsum equals `coeff_01 F * c = 1 * c = c`.
  congr 1
  -- Show: ∑ᶠ d, coeff d F • (if d 0 = 0 ∧ d 1 = 1 then c else 0) = c.
  rw [finsum_eq_single _ (Finsupp.single (1 : Fin 2) 1) (by
    intro d hd
    have : ¬ (d 0 = 0 ∧ d 1 = 1) := by
      intro ⟨h0, h1⟩
      apply hd
      ext i
      fin_cases i <;> simp [Finsupp.single_apply, h0, h1]
    rw [if_neg this, smul_zero])]
  -- Eval at d = Finsupp.single 1 1: d 0 = 0, d 1 = 1.
  have hd01 : (Finsupp.single (1 : Fin 2) 1) 0 = 0 := by
    simp [Finsupp.single_apply]
  have hd11 : (Finsupp.single (1 : Fin 2) 1) 1 = 1 := by
    simp [Finsupp.single_apply]
  rw [hd01, hd11]
  rw [if_pos ⟨rfl, rfl⟩]
  -- coeff (Finsupp.single 1 1) F.toSeries = 1 by the right-unit axiom.
  rw [HasseWeil.FG.FormalGroup.coeff_01, one_smul]

/-! ### Core invariant and functional equation -/

/-- **Core invariant**: for `k ≤ n`,
`coeff k (fAdd F X (inverseTrunc F n)) = 0`.

By induction on `n`:
- `n = 0`: `inverseTrunc F 0 = 0`, and `fAdd F X 0 = X` (by `fAdd_zero_right`).
  So `coeff k X = 0` for `k = 0`.
- `n → n+1`: use stabilization (Lemma `coeff_fAdd_X_eq_of_coeff_eq`) for `k ≤ n`
  and monomial-addition (Lemma `coeff_fAdd_X_add_monomial`) for `k = n+1`,
  noting that the correction `c = -coeff (n+1) (fAdd F X prev)` exactly cancels
  the previous coefficient. -/
theorem FormalGroup.inverseTrunc_fAdd_coeff_eq_zero
    (F : FormalGroup R) (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k
        (HasseWeil.FG.fAdd F PowerSeries.X (F.inverseTrunc n)) = 0 := by
  induction n with
  | zero =>
    -- k = 0.
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    -- fAdd F X 0 = X (by fAdd_zero_right).
    have hXcc : @PowerSeries.constantCoeff R _ PowerSeries.X = 0 := by simp
    rw [FormalGroup.inverseTrunc_zero]
    rw [HasseWeil.FG.fAdd_zero_right F PowerSeries.X hXcc]
    -- coeff 0 X = 0.
    rw [PowerSeries.coeff_zero_X]
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · -- k ≤ n: use stabilization + ih.
      have hk'' : k ≤ n := Nat.lt_succ_iff.mp hk'
      -- fAdd F X (inverseTrunc F (n+1)) and fAdd F X (inverseTrunc F n) agree on
      -- coefficients up to degree n, so coeff k of both is equal (and ih gives 0).
      have hstab : ∀ j ≤ n,
          PowerSeries.coeff j (F.inverseTrunc (n + 1)) =
            PowerSeries.coeff j (F.inverseTrunc n) := by
        intro j hj
        exact F.coeff_inverseTrunc_succ_of_le n j hj
      rw [FormalGroup.coeff_fAdd_X_eq_of_coeff_eq F _ _
            (F.inverseTrunc_constantCoeff (n + 1))
            (F.inverseTrunc_constantCoeff n)
            n hstab k hk'']
      exact ih hk''
    · -- k = n + 1.
      have hk_eq : k = n + 1 := le_antisymm hk hk'
      subst hk_eq
      -- inverseTrunc F (n+1) = inverseTrunc F n + C c * X^(n+1) where
      -- c = -coeff (n+1) (fAdd F X (inverseTrunc F n)).
      set prev := F.inverseTrunc n with hprev
      set curr := HasseWeil.FG.fAdd F PowerSeries.X prev with hcurr
      have hunfold : F.inverseTrunc (n + 1) = prev +
          PowerSeries.C (-PowerSeries.coeff (n + 1) curr) * PowerSeries.X ^ (n + 1) := rfl
      rw [hunfold]
      -- Apply monomial-addition.
      rw [FormalGroup.coeff_fAdd_X_add_monomial F prev n
            (-PowerSeries.coeff (n + 1) curr) (F.inverseTrunc_constantCoeff n)]
      -- Goal: coeff (n+1) curr + (-coeff (n+1) curr) = 0.
      show PowerSeries.coeff (n + 1) curr + -PowerSeries.coeff (n + 1) curr = 0
      exact add_neg_cancel _

/-- **Functional equation of the formal inverse** (Silverman IV.2, closing
T-IV-2-011): `F(T, i(T)) = 0`, i.e., `fAdd F X (inverse F) = 0`.

This is the defining identity of the formal inverse. The proof uses the
polynomial-tail / substitution-stabilization / induction pattern: at each
degree `k`, `fAdd F X (inverse F)` agrees with `fAdd F X (inverseTrunc F k)`,
and the latter vanishes at degree `k` by the core invariant. -/
theorem FormalGroup.fAdd_X_inverse_eq_zero (F : FormalGroup R) :
    HasseWeil.FG.fAdd F PowerSeries.X F.inverse = 0 := by
  -- Extensional: coeff k agrees for all k.
  ext k
  -- The `0` RHS has coeff k = 0 for all k.
  rw [map_zero]
  -- `inverse F` and `inverseTrunc F k` agree on coefficients up to degree k.
  have hstab : ∀ j ≤ k,
      PowerSeries.coeff j F.inverse = PowerSeries.coeff j (F.inverseTrunc k) := by
    intro j hj
    change PowerSeries.coeff j (PowerSeries.mk F.inverseCoeff) = _
    rw [PowerSeries.coeff_mk]
    rw [F.coeff_inverseTrunc_of_le k j hj]
  -- Apply stabilization to the LHS: coeff k (fAdd F X (inverse F)) =
  -- coeff k (fAdd F X (inverseTrunc F k)).
  rw [FormalGroup.coeff_fAdd_X_eq_of_coeff_eq F F.inverse (F.inverseTrunc k)
        F.inverse_constantCoeff
        (F.inverseTrunc_constantCoeff k)
        k hstab k le_rfl]
  -- Apply invariant: coeff k (fAdd F X (inverseTrunc F k)) = 0.
  exact F.inverseTrunc_fAdd_coeff_eq_zero k k le_rfl

end InversionProof

end HasseWeil.FormalGroup

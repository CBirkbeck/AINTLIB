import HasseWeil.FormalGroup.InvariantDiff
import Mathlib.Algebra.Module.Rat

/-!
# The formal logarithm of a formal group (Silverman IV.5)

For a formal group `F` over a `ℚ`-algebra `R` (or more generally a ring with a
`Module ℚ R` structure), the **formal logarithm**

`log_F(T) := ∫₀^T ω_F(s) ds = T + (c₁/2) T² + (c₂/3) T³ + ⋯`

is the integral of the normalized invariant differential
`ω_F(T) = 1 + c₁T + c₂T² + ⋯`. It is a power series with
constant term `0` and linear coefficient `1`.

## Main definition

* `HasseWeil.FormalGroup.FormalGroup.log F` — the formal logarithm of `F`,
  defined over any commutative ring `R` equipped with a `ℚ`-module structure.

## Main results

* `FormalGroup.log_coeff_zero` — `constantCoeff (log F) = 0`.
* `FormalGroup.log_coeff_succ` — `coeff (n + 1) (log F) = (1/(n+1)) • coeff n ω_F`.
* `FormalGroup.log_coeff_one` — `coeff 1 (log F) = 1`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.5.
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-- The **formal logarithm** of a formal group `F` over a ring `R` with a
`Module ℚ R` structure.

Concretely, if `ω_F(T) = 1 + c₁T + c₂T² + ⋯`, then
`log_F(T) = T + (c₁/2)T² + (c₂/3)T³ + ⋯ = ∑ (c_{n-1}/n)·T^n`.

The coefficient at `T^n` for `n ≥ 1` is the ℚ-scalar multiple
`((n : ℚ)⁻¹) • (coeff of ω_F at n - 1)`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.5. -/
noncomputable def FormalGroup.log (F : FormalGroup R) [Module ℚ R] :
    PowerSeries R :=
  PowerSeries.mk fun n ↦
    if n = 0 then 0
    else ((n : ℚ)⁻¹) •
      PowerSeries.coeff (n - 1) F.normalizedDifferential.toSeries

/-- The coefficient formula for `log F` at degree `n + 1`:
`coeff (n + 1) (log F) = (1/(n+1)) • coeff n ω_F`. -/
theorem FormalGroup.log_coeff_succ (F : FormalGroup R) [Module ℚ R] (n : ℕ) :
    PowerSeries.coeff (n + 1) F.log =
      ((n + 1 : ℚ)⁻¹) •
        PowerSeries.coeff n F.normalizedDifferential.toSeries := by
  simp [FormalGroup.log, PowerSeries.coeff_mk]

/-- The constant coefficient of `log F` is zero. -/
@[simp]
theorem FormalGroup.log_coeff_zero (F : FormalGroup R) [Module ℚ R] :
    PowerSeries.coeff 0 F.log = 0 := by
  simp [FormalGroup.log, PowerSeries.coeff_mk]

/-- `constantCoeff (log F) = 0`. -/
@[simp]
theorem FormalGroup.log_constantCoeff (F : FormalGroup R) [Module ℚ R] :
    @PowerSeries.constantCoeff R _ F.log = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact F.log_coeff_zero

/-- The linear coefficient of `log F` is `1`, reflecting that
`log_F(T) = T + O(T²)`. -/
@[simp]
theorem FormalGroup.log_coeff_one (F : FormalGroup R) [Module ℚ R] :
    PowerSeries.coeff 1 F.log = 1 := by
  have : PowerSeries.coeff 1 F.log = ((1 : ℚ)⁻¹) •
      PowerSeries.coeff 0 F.normalizedDifferential.toSeries := by
    simpa using F.log_coeff_succ 0
  rw [this, inv_one, one_smul]
  -- coeff 0 ω_F = constantCoeff ω_F = 1 since ω_F is normalized.
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact F.normalizedDifferential_isNormalized

/-! ### The formal exponential

We construct `exp_F` as the compositional inverse of `log_F` via an iterative
truncation argument.

Let `f : PowerSeries R` with `coeff 0 f = 0` and `coeff 1 f = 1`
(e.g., `f = log_F`). We build the compositional inverse `g` incrementally:

* `compInvTrunc f 0 = 0`.
* `compInvTrunc f (n+1) = compInvTrunc f n + c · T^(n+1)` where the correction
  `c` is chosen so that `coeff (n+1) (f ∘ compInvTrunc f (n+1)) = [n+1 = 1]`
  (Kronecker delta). Since `f = T + O(T²)`, this determines `c` uniquely:
  `c = δ_{1, n+1} - coeff (n+1) (f(compInvTrunc f n))`.

By induction, `compInvTrunc f n` has the correct coefficients up to degree `n`,
and adding a `T^(n+1)` correction doesn't change any lower coefficient.
The compositional inverse is recovered by taking the `n`-th coefficient of
`compInvTrunc f n`. -/

/-- Iterative truncation of the compositional inverse of `f`.
At each step we add a correction of the form `c · T^(n+1)` chosen to zero out
(or set to 1 for `n+1 = 1`) the `(n+1)`-th coefficient of `f ∘ prev`. -/
noncomputable def compInvTrunc (f : PowerSeries R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 =>
    let prev := compInvTrunc f n
    let current := PowerSeries.subst prev f
    let c : R :=
      if n + 1 = 1 then 1 - PowerSeries.coeff 1 current
      else -PowerSeries.coeff (n + 1) current
    prev + PowerSeries.C c * PowerSeries.X ^ (n + 1)

/-- The `n`-th coefficient of the compositional inverse of `f`. -/
noncomputable def compInvCoeff (f : PowerSeries R) (n : ℕ) : R :=
  PowerSeries.coeff n (compInvTrunc f n)

/-- The **formal compositional inverse** of `f : PowerSeries R`.

Assuming `coeff 0 f = 0` and `coeff 1 f = 1`, this is the power series `g`
characterized by `f ∘ g = X` (compositional inverse). Defined
coefficient-by-coefficient via `compInvCoeff`.

The full compositional inverse identity `PowerSeries.subst (compInverse f) f = X`
under the hypotheses `constantCoeff f = 0` and `coeff 1 f = 1` is stated as
`subst_compInverse_eq_X` (future work; definition is sufficient for downstream
use as the compositional inverse API).

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2, IV.5. -/
noncomputable def compInverse (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (compInvCoeff f)

/-- `compInvTrunc f 0 = 0`. -/
@[simp]
theorem compInvTrunc_zero (f : PowerSeries R) : compInvTrunc f 0 = 0 :=
  rfl

/-- `compInvCoeff f 0 = 0`. -/
@[simp]
theorem compInvCoeff_zero (f : PowerSeries R) : compInvCoeff f 0 = 0 := by
  simp [compInvCoeff]

/-- The zeroth coefficient of `compInverse f` is zero. -/
@[simp]
theorem compInverse_coeff_zero (f : PowerSeries R) :
    PowerSeries.coeff 0 (compInverse f) = 0 := by
  simp [compInverse]

/-- `constantCoeff (compInverse f) = 0`. -/
@[simp]
theorem compInverse_constantCoeff (f : PowerSeries R) :
    @PowerSeries.constantCoeff R _ (compInverse f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact compInverse_coeff_zero f

/-- The linear coefficient of `subst 0 f` is zero. Auxiliary for
`compInverse_coeff_one`. -/
private theorem coeff_one_subst_zero (f : PowerSeries R) :
    PowerSeries.coeff 1 (PowerSeries.subst (0 : PowerSeries R) f) = 0 := by
  rw [PowerSeries.coeff_subst' PowerSeries.HasSubst.zero' f 1]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  -- coeff 1 (0^d) = 0 in all cases.
  by_cases hd : d = 0
  · -- d = 0: 0^0 = 1, coeff 1 1 = 0.
    subst hd
    have h0 : PowerSeries.coeff 1 ((0 : PowerSeries R) ^ 0) = 0 := by
      rw [pow_zero]
      change MvPowerSeries.coeff (Finsupp.single () 1) (1 : MvPowerSeries Unit R) = 0
      simp [MvPowerSeries.coeff_one]
    rw [h0, smul_zero]
  · -- d ≠ 0: 0^d = 0, coeff 1 0 = 0.
    have h0 : ((0 : PowerSeries R) ^ d) = 0 := zero_pow hd
    rw [h0, map_zero, smul_zero]

/-- The linear coefficient of `compInverse f` is always `1`, regardless of `f`.
This is true unconditionally because the iterative construction in
`compInvTrunc` chooses `c = 1` at the first step, ensuring the linear
coefficient is fixed at `1`. -/
@[simp]
theorem compInverse_coeff_one (f : PowerSeries R) :
    PowerSeries.coeff 1 (compInverse f) = 1 := by
  -- Unfold `compInverse f = mk (compInvCoeff f)`, so `coeff 1 = compInvCoeff f 1`.
  change PowerSeries.coeff 1 (PowerSeries.mk (compInvCoeff f)) = 1
  rw [PowerSeries.coeff_mk]
  -- `compInvCoeff f 1 = coeff 1 (compInvTrunc f 1)`.
  change PowerSeries.coeff 1 (compInvTrunc f 1) = 1
  -- Unfold the recursive step.
  change PowerSeries.coeff 1
      (compInvTrunc f 0 +
        PowerSeries.C
          (if (0 + 1 : ℕ) = 1 then 1 - PowerSeries.coeff 1
              (PowerSeries.subst (compInvTrunc f 0) f)
           else -PowerSeries.coeff (0 + 1)
              (PowerSeries.subst (compInvTrunc f 0) f)) *
        PowerSeries.X ^ (0 + 1)) = 1
  rw [compInvTrunc_zero, if_pos rfl, coeff_one_subst_zero, sub_zero, zero_add]
  -- Goal: coeff 1 (C 1 * X^1) = 1.
  simp

/-! ### Compositional inverse identity

The full compositional-inverse identity is `PowerSeries.subst (compInverse f) f = X`,
assuming `constantCoeff f = 0` and `coeff 1 f = 1`. Its proof proceeds in four steps:

1. **Polynomial-tail decomposition of `compInvTrunc`**: every truncation
   `compInvTrunc f n` is of the form "stuff at degree ≤ n, zero elsewhere".
   In particular, coefficients stabilise: for `k ≤ n`,
   `coeff k (compInvTrunc f n) = compInvCoeff f k = coeff k (compInverse f)`.
2. **Substitution stabilisation**: if `g₁` and `g₂` have zero constant term
   and agree up to degree `n`, then `subst g₁ f` and `subst g₂ f` agree up
   to degree `n`. Formally, `coeff k (subst g₁ f) = coeff k (subst g₂ f)`
   for every `k ≤ n`.
3. **Core invariant**: by construction,
   `coeff k (subst (compInvTrunc f n) f) = (if k = 1 then 1 else 0)`
   for every `k ≤ n`, provided `constantCoeff f = 0` and `coeff 1 f = 1`.
   The inductive step uses step (2) plus the definition of the correction
   coefficient `c` in `compInvTrunc f (n+1) = compInvTrunc f n + C c * X^(n+1)`.
4. **Conclusion**: by steps (1)–(3),
   `coeff k (subst (compInverse f) f) = coeff k (subst (compInvTrunc f k) f)
     = if k = 1 then 1 else 0 = coeff k X`.
-/

section CompInverseProof

variable {R : Type*} [CommRing R]

open PowerSeries in
/-- `compInvTrunc f (n+1)` differs from `compInvTrunc f n` only by a
monomial of degree `n+1`; in particular its lower coefficients coincide. -/
theorem coeff_compInvTrunc_succ_of_le (f : PowerSeries R) (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k (compInvTrunc f (n + 1)) =
      PowerSeries.coeff k (compInvTrunc f n) := by
  -- Unfold the recursive definition.
  change PowerSeries.coeff k
      (compInvTrunc f n +
        PowerSeries.C _ * PowerSeries.X ^ (n + 1)) = _
  rw [map_add, PowerSeries.coeff_C_mul_X_pow]
  -- `k ≠ n + 1` since `k ≤ n`.
  rw [if_neg (by omega : k ≠ n + 1), add_zero]

open PowerSeries in
/-- For `k ≤ n`, the `k`-th coefficient of `compInvTrunc f n` equals the
stable coefficient `compInvCoeff f k`. -/
theorem coeff_compInvTrunc_of_le (f : PowerSeries R) (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k (compInvTrunc f n) = compInvCoeff f k := by
  induction n with
  | zero =>
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    simp [compInvCoeff]
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hk'' : k ≤ n := Nat.lt_succ_iff.mp hk'
      rw [coeff_compInvTrunc_succ_of_le f n k hk''] -- reduce to `compInvTrunc f n`
      exact ih hk''
    · -- `k = n + 1`, direct from definition of `compInvCoeff`.
      have : k = n + 1 := le_antisymm hk hk'
      subst this
      rfl

open PowerSeries in
/-- `compInvTrunc f n` has zero constant coefficient. -/
theorem compInvTrunc_constantCoeff (f : PowerSeries R) (n : ℕ) :
    @PowerSeries.constantCoeff R _ (compInvTrunc f n) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_compInvTrunc_of_le f n 0 (Nat.zero_le _)]
  simp

open PowerSeries in
/-- `compInvTrunc f n` admits substitution (zero constant coefficient). -/
theorem compInvTrunc_hasSubst (f : PowerSeries R) (n : ℕ) :
    PowerSeries.HasSubst (compInvTrunc f n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (compInvTrunc_constantCoeff f n)

open PowerSeries in
/-- `compInverse f` admits substitution. -/
theorem compInverse_hasSubst (f : PowerSeries R) :
    PowerSeries.HasSubst (compInverse f) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (compInverse_constantCoeff f)

open PowerSeries in
/-- If `g₁` and `g₂` agree up to degree `n`, then so do their powers: for each
`d`, the coefficients `coeff k (g₁^d) = coeff k (g₂^d)` for every `k ≤ n`. -/
theorem coeff_pow_eq_of_coeff_eq (g₁ g₂ : PowerSeries R)
    (n : ℕ) (hg : ∀ j ≤ n, PowerSeries.coeff j g₁ = PowerSeries.coeff j g₂)
    (d : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k (g₁ ^ d) = PowerSeries.coeff k (g₂ ^ d) := by
  induction d with
  | zero =>
    intro k _
    simp
  | succ d ih =>
    intro k hk
    have hstep : ∀ g : PowerSeries R, g ^ (d + 1) = g * g ^ d := by
      intro g
      rw [pow_succ]
      exact mul_comm _ _
    rw [hstep g₁, hstep g₂, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨i, j⟩ hij
    have hij' : i + j = k := Finset.mem_antidiagonal.mp hij
    have hi_le : i ≤ n := by omega
    have hj_le : j ≤ n := by omega
    rw [hg i hi_le, ih j hj_le]

open PowerSeries in
/-- Substitution stabilisation: if `g₁` and `g₂` have zero constant coefficients
and agree up to degree `n`, then `coeff k (subst g₁ f) = coeff k (subst g₂ f)`
for every `k ≤ n`. -/
theorem coeff_subst_eq_of_coeff_eq (f g₁ g₂ : PowerSeries R)
    (h1 : @PowerSeries.constantCoeff R _ g₁ = 0)
    (h2 : @PowerSeries.constantCoeff R _ g₂ = 0)
    (n : ℕ) (hg : ∀ j ≤ n, PowerSeries.coeff j g₁ = PowerSeries.coeff j g₂)
    (k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k (PowerSeries.subst g₁ f) =
      PowerSeries.coeff k (PowerSeries.subst g₂ f) := by
  have hs1 : PowerSeries.HasSubst g₁ := PowerSeries.HasSubst.of_constantCoeff_zero' h1
  have hs2 : PowerSeries.HasSubst g₂ := PowerSeries.HasSubst.of_constantCoeff_zero' h2
  rw [PowerSeries.coeff_subst' hs1, PowerSeries.coeff_subst' hs2]
  apply finsum_congr
  intro d
  congr 1
  -- Two cases: either the power `d` is within reach (`d ≤ k`) — then we use
  -- `coeff_pow_eq_of_coeff_eq`; or `d > k`, in which case both sides are zero.
  by_cases hdk : d ≤ k
  · exact coeff_pow_eq_of_coeff_eq g₁ g₂ n hg d k hk
  · push Not at hdk
    have hzero : ∀ (g : PowerSeries R), @PowerSeries.constantCoeff R _ g = 0 →
        PowerSeries.coeff k (g ^ d) = 0 := by
      intro g hg0
      have horder : (d : ℕ∞) ≤ (g ^ d).order :=
        PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg0
      have hcast : (k : ℕ∞) < (d : ℕ∞) := ENat.coe_lt_coe.mpr hdk
      have : (k : ℕ∞) < (g ^ d).order := lt_of_lt_of_le hcast horder
      exact PowerSeries.coeff_of_lt_order k this
    rw [hzero g₁ h1, hzero g₂ h2]

/-! ### Key lemma for the induction step

The critical computation: when we add a monomial correction `C c * X^(n+1)` to
a series `g` with zero constant coefficient, the coefficient of `X^(n+1)` in
`subst (g + C c X^(n+1)) f` increases by `c * coeff 1 f`. -/

open PowerSeries in
/-- If `g` has zero constant coefficient, then `coeff k (g^d)` for `d > k`
vanishes. -/
theorem coeff_pow_eq_zero_of_gt (g : PowerSeries R)
    (hg : @PowerSeries.constantCoeff R _ g = 0) (k d : ℕ) (hdk : k < d) :
    PowerSeries.coeff k (g ^ d) = 0 := by
  have horder : (d : ℕ∞) ≤ (g ^ d).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg
  have hcast : (k : ℕ∞) < (d : ℕ∞) := ENat.coe_lt_coe.mpr hdk
  exact PowerSeries.coeff_of_lt_order k (lt_of_lt_of_le hcast horder)

/-! ### Monomial auxiliary lemmas -/

open PowerSeries in
/-- `C c * X^(n+1)` has zero constant coefficient. -/
theorem monomial_constantCoeff_zero (n : ℕ) (c : R) :
    @PowerSeries.constantCoeff R _ (PowerSeries.C c * PowerSeries.X ^ (n + 1)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_C_mul_X_pow]
  simp

open PowerSeries in
/-- The `j`-th power of a monomial: `(C c * X^(n+1))^j = C (c^j) * X^(j*(n+1))`. -/
theorem monomial_pow_eq (n : ℕ) (c : R) (j : ℕ) :
    (PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ j =
      PowerSeries.C (c ^ j) * PowerSeries.X ^ (j * (n + 1)) := by
  have h1 : (PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ j =
      (PowerSeries.C c) ^ j * ((PowerSeries.X : PowerSeries R) ^ (n + 1)) ^ j :=
    mul_pow _ _ _
  rw [h1]
  rw [← map_pow]
  rw [← pow_mul]
  rw [mul_comm j (n + 1)]

open PowerSeries in
/-- For the monomial `h = C c * X^(n+1)`, any `i`-th power for `i ≥ 2` has
coefficient at `n+1` equal to `0`, because its order is `≥ 2(n+1) > n+1`. -/
theorem coeff_monomial_pow_high (n : ℕ) (c : R) (i : ℕ) (hi : 2 ≤ i) :
    PowerSeries.coeff (n + 1) ((PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ i) = 0 := by
  rw [monomial_pow_eq]
  rw [PowerSeries.coeff_C_mul_X_pow]
  rw [if_neg]
  intro heq
  -- n + 1 = i * (n + 1) with i ≥ 2 contradicts n + 1 ≥ 1.
  nlinarith

open PowerSeries in
/-- Key fact: `coeff (n+1) ((g + h) ^ d) = coeff (n+1) (g^d) + (if d = 1 then c else 0)`,
where `h = C c * X^(n+1)` and `g` has zero constant coefficient. -/
theorem coeff_add_monomial_pow_eq (g : PowerSeries R)
    (hg : @PowerSeries.constantCoeff R _ g = 0) (n : ℕ) (c : R) (d : ℕ) :
    PowerSeries.coeff (n + 1)
        ((g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ d) =
      PowerSeries.coeff (n + 1) (g ^ d) + (if d = 1 then c else 0) := by
  set h : PowerSeries R := PowerSeries.C c * PowerSeries.X ^ (n + 1) with hdef
  -- Expand via commuted add_pow.
  have hcomm : (h + g) ^ d =
      ∑ m ∈ Finset.range (d + 1), h ^ m * g ^ (d - m) * (d.choose m : PowerSeries R) :=
    add_pow h g d
  rw [show g + h = h + g from add_comm g h, hcomm]
  rw [map_sum]
  -- Helper: `(k : ℕ) → PowerSeries R` via nat-cast equals `C (k : R)`.
  have hnatCast : ∀ k : ℕ, ((k : ℕ) : PowerSeries R) = PowerSeries.C ((k : ℕ) : R) := by
    intro k
    induction k with
    | zero =>
      push_cast
      exact (map_zero _).symm
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : PowerSeries R) = ((k : ℕ) : PowerSeries R) + 1 from by push_cast; rfl]
      rw [ih]
      rw [show ((k + 1 : ℕ) : R) = ((k : ℕ) : R) + 1 from by push_cast; rfl]
      rw [map_add, map_one]
  have hterm : ∀ m : ℕ,
      PowerSeries.coeff (n + 1) (h ^ m * g ^ (d - m) * (d.choose m : PowerSeries R)) =
        (d.choose m : R) * PowerSeries.coeff (n + 1) (h ^ m * g ^ (d - m)) := by
    intro m
    rw [hnatCast]
    rw [show h ^ m * g ^ (d - m) * PowerSeries.C ((d.choose m : ℕ) : R) =
            PowerSeries.C ((d.choose m : ℕ) : R) * (h ^ m * g ^ (d - m)) from
        mul_comm _ _]
    rw [PowerSeries.coeff_C_mul]
  simp_rw [hterm]
  -- Case analysis on d.
  match d with
  | 0 =>
    -- d = 0: Σ over {0} of h^0 * g^0 * 1 = coeff 0 * coeff (n+1) 1 = 0.
    rw [Finset.sum_range_one]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, pow_zero, Nat.sub_self, mul_one]
    rw [if_neg (by decide : (0 : ℕ) ≠ 1)]
    rw [add_zero]
  | 1 =>
    -- d = 1: Σ over {0, 1}.
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    -- Compute all involved factors explicitly.
    change (((1 : ℕ).choose 0 : R)) * PowerSeries.coeff (n + 1) (h ^ 0 * g ^ (1 - 0))
          + (((1 : ℕ).choose 1 : R)) * PowerSeries.coeff (n + 1) (h ^ 1 * g ^ (1 - 1))
            = PowerSeries.coeff (n + 1) (g ^ 1) + (if (1 : ℕ) = 1 then c else 0)
    -- Evaluate: 1 - 0 = 1, 1 - 1 = 0, choose 1 0 = 1, choose 1 1 = 1.
    rw [Nat.choose_zero_right, Nat.choose_one_right]
    rw [show (1 - 0 : ℕ) = 1 from rfl, show (1 - 1 : ℕ) = 0 from rfl]
    rw [show (g ^ 1 : PowerSeries R) = g from pow_one _]
    rw [show (h ^ 0 : PowerSeries R) = 1 from pow_zero _]
    rw [show (h ^ 1 : PowerSeries R) = h from pow_one _]
    rw [show (g ^ 0 : PowerSeries R) = 1 from pow_zero _]
    rw [if_pos rfl]
    -- Goal: 1 * coeff (n+1) (1 * g) + 1 * coeff (n+1) (h * 1) = coeff (n+1) g + c
    simp only [Nat.cast_one, one_mul, mul_one]
    -- Goal: coeff (n+1) g + coeff (n+1) h = coeff (n+1) g + c
    rw [show PowerSeries.coeff (n + 1) h = c from by
          rw [hdef, PowerSeries.coeff_C_mul_X_pow, if_pos rfl]]
  | d + 2 =>
    -- d + 2 ≥ 2. Split into {0, 1, 2, ..., d+1, d+2}.
    -- We'll extract m = 0 and m = 1 via Finset.sum_range_succ twice (from the low end).
    -- But Finset.sum_range_succ extracts the TOP. So we use Finset.sum_range_succ'.
    -- Plan: handle m = 0 and m = 1 directly by induction on the whole range.
    -- For clarity use the split into {0, 1} ∪ filter (2 ≤ ·).
    rw [show Finset.range (d + 2 + 1) =
            insert 0 (insert 1 ((Finset.range (d + 2 + 1)).filter (2 ≤ ·))) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      omega]
    rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      omega)]
    rw [Finset.sum_insert (by
      simp only [Finset.mem_filter, Finset.mem_range]
      omega)]
    -- Compute m=0 term: choose(d+2, 0) = 1, h^0 = 1, g^(d+2-0) = g^(d+2).
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul, pow_zero]
    -- Compute m=1 term: choose(d+2, 1) = d+2, h^1 = h, g^(d+2-1) = g^(d+1).
    rw [Nat.choose_one_right]
    rw [show (h ^ 1 : PowerSeries R) * g ^ (d + 2 - 1) = h * g ^ (d + 1) from by
      rw [pow_one, show d + 2 - 1 = d + 1 from by omega]]
    -- Show the m ≥ 2 sum is 0.
    have hhigh :
        (∑ m ∈ (Finset.range (d + 2 + 1)).filter (2 ≤ ·),
          (↑((d + 2).choose m) : R) *
            PowerSeries.coeff (n + 1) (h ^ m * g ^ (d + 2 - m))) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨_, hm2⟩ := hm
      -- coeff (n+1) (h^m * g^(d+2-m)) = 0: h^m has order m*(n+1) > n+1.
      have hcoeff_zero : PowerSeries.coeff (n + 1) (h ^ m * g ^ (d + 2 - m)) = 0 := by
        rw [PowerSeries.coeff_mul]
        apply Finset.sum_eq_zero
        intro ⟨a, b⟩ hab
        have hab' : a + b = n + 1 := Finset.mem_antidiagonal.mp hab
        rw [hdef, monomial_pow_eq, PowerSeries.coeff_C_mul_X_pow]
        split_ifs with heq
        · exfalso
          nlinarith
        · simp
      rw [hcoeff_zero]
      rw [mul_zero]
    rw [hhigh, add_zero]
    -- Goal: [coeff (n+1) g^(d+2)] + [d+2 * coeff (n+1) (h * g^(d+1))] = coeff (n+1) g^(d+2) + 0
    rw [if_neg (by omega : d + 2 ≠ 1)]
    rw [add_zero]
    -- Show coeff (n+1) (h * g^(d+1)) = 0 since g^(d+1) has constantCoeff 0 for d ≥ 0.
    have : PowerSeries.coeff (n + 1) (h * g ^ (d + 1)) = 0 := by
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro ⟨a, b⟩ hab
      have hab' : a + b = n + 1 := Finset.mem_antidiagonal.mp hab
      rw [hdef, PowerSeries.coeff_C_mul_X_pow]
      split_ifs with ha
      · have hb : b = 0 := by omega
        subst hb
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hg, zero_pow (by omega)]
        simp
      · simp
    rw [this, mul_zero, add_zero]

open PowerSeries in
/-- Key identity for the induction step: when we add a monomial `C c * X^(n+1)`
to `g` (with zero constant coefficient), the `(n+1)`-th coefficient of the
substitution `subst (g + C c * X^(n+1)) f` increases by exactly `c * coeff 1 f`. -/
theorem coeff_subst_add_monomial (f g : PowerSeries R) (n : ℕ) (c : R)
    (hg : @PowerSeries.constantCoeff R _ g = 0) :
    PowerSeries.coeff (n + 1)
        (PowerSeries.subst (g + PowerSeries.C c * PowerSeries.X ^ (n + 1)) f) =
      PowerSeries.coeff (n + 1) (PowerSeries.subst g f) + c * PowerSeries.coeff 1 f := by
  set h : PowerSeries R := PowerSeries.C c * PowerSeries.X ^ (n + 1) with hdef
  have hh : @PowerSeries.constantCoeff R _ h = 0 := monomial_constantCoeff_zero n c
  have hgh : @PowerSeries.constantCoeff R _ (g + h) = 0 := by simp [hg, hh]
  have hsubG : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hsubGH : PowerSeries.HasSubst (g + h) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hgh
  rw [PowerSeries.coeff_subst' hsubGH, PowerSeries.coeff_subst' hsubG]
  -- Use coeff_add_monomial_pow_eq for each d.
  have key : ∀ d : ℕ,
      PowerSeries.coeff (n + 1) ((g + h) ^ d) =
        PowerSeries.coeff (n + 1) (g ^ d) + (if d = 1 then c else 0) :=
    fun d ↦ coeff_add_monomial_pow_eq g hg n c d
  -- Linearity of finsum over smul.
  have hadd : ∀ d : ℕ,
      PowerSeries.coeff d f • PowerSeries.coeff (n + 1) ((g + h) ^ d) =
        PowerSeries.coeff d f • PowerSeries.coeff (n + 1) (g ^ d) +
          PowerSeries.coeff d f • (if d = 1 then c else 0) := by
    intro d
    rw [key d, smul_add]
  rw [show (fun d ↦ PowerSeries.coeff d f • PowerSeries.coeff (n + 1) ((g + h) ^ d)) =
          (fun d ↦ PowerSeries.coeff d f • PowerSeries.coeff (n + 1) (g ^ d) +
            PowerSeries.coeff d f • (if d = 1 then c else 0)) from funext hadd]
  rw [finsum_add_distrib
    (PowerSeries.coeff_subst_finite' hsubG f (n + 1))
    (by
      apply Set.Finite.subset (Set.finite_singleton 1)
      intro d hd
      simp only [Function.mem_support, smul_ite, smul_zero, ne_eq] at hd
      by_contra h1
      simp [show d ≠ 1 from h1] at hd)]
  -- The singular sum equals coeff 1 f * c.
  congr 1
  rw [finsum_eq_single _ 1 (by
    intro d hd
    rw [if_neg hd, smul_zero])]
  rw [if_pos rfl, smul_eq_mul, mul_comm]

/-! ### The core invariant and the compositional-inverse identity -/

open PowerSeries in
/-- **Core invariant**: for `k ≤ n`, the `k`-th coefficient of the
substitution `subst (compInvTrunc f n) f` equals the Kronecker delta `[k = 1]`,
assuming `constantCoeff f = 0` and `coeff 1 f = 1`.

This is the essence of the iterative construction: each step `n+1` introduces
a correction chosen precisely to make the `(n+1)`-th coefficient of
`subst (compInvTrunc f (n+1)) f` match `[n+1 = 1]`, and earlier coefficients
are preserved by substitution stabilisation. -/
theorem compInvTrunc_subst_coeff_eq (f : PowerSeries R)
    (h0 : @PowerSeries.constantCoeff R _ f = 0) (h1 : PowerSeries.coeff 1 f = 1)
    (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k (PowerSeries.subst (compInvTrunc f n) f) =
      (if k = 1 then 1 else 0) := by
  induction n with
  | zero =>
    -- k ≤ 0 means k = 0.
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    simp only [compInvTrunc_zero]
    -- coeff 0 (subst 0 f) = constantCoeff (subst 0 f) = 0.
    have : PowerSeries.coeff 0 (PowerSeries.subst (0 : PowerSeries R) f) = 0 := by
      have hz : @PowerSeries.constantCoeff R _ (0 : PowerSeries R) = 0 := by simp
      have hmv : MvPowerSeries.constantCoeff (PowerSeries.subst (0 : PowerSeries R) f) = 0 :=
        PowerSeries.constantCoeff_subst_eq_zero hz f h0
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hmv
    rw [this]
    simp
  | succ n ih =>
    -- Case split on whether k ≤ n or k = n + 1.
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · -- k ≤ n: use substitution stabilization + ih.
      have hk'' : k ≤ n := Nat.lt_succ_iff.mp hk'
      -- coeff k (subst (compInvTrunc f (n+1)) f) = coeff k (subst (compInvTrunc f n) f)
      -- by coeff_subst_eq_of_coeff_eq since compInvTrunc f (n+1) and compInvTrunc f n
      -- agree up to degree n.
      have hstab : ∀ j ≤ n,
          PowerSeries.coeff j (compInvTrunc f (n + 1)) =
            PowerSeries.coeff j (compInvTrunc f n) := by
        intro j hj
        exact coeff_compInvTrunc_succ_of_le f n j hj
      rw [coeff_subst_eq_of_coeff_eq f _ _
            (compInvTrunc_constantCoeff f (n + 1))
            (compInvTrunc_constantCoeff f n)
            n hstab k hk'']
      exact ih hk''
    · -- k = n + 1.
      have hk_eq : k = n + 1 := le_antisymm hk hk'
      subst hk_eq
      -- Unfold: compInvTrunc f (n+1) = compInvTrunc f n + C c * X^(n+1).
      -- Use coeff_subst_add_monomial.
      set prev := compInvTrunc f n with hprev
      set prev' := PowerSeries.subst prev f with hprev'
      have hunfold : compInvTrunc f (n + 1) = prev +
          PowerSeries.C (if n + 1 = 1 then 1 - PowerSeries.coeff 1 prev'
            else -PowerSeries.coeff (n + 1) prev') *
              PowerSeries.X ^ (n + 1) := rfl
      rw [hunfold]
      rw [coeff_subst_add_monomial f prev n _
            (compInvTrunc_constantCoeff f n)]
      rw [h1, mul_one]
      -- Goal: coeff (n+1) prev' + (if n+1=1 then 1 - coeff 1 prev' else -coeff (n+1) prev')
      --     = if n+1=1 then 1 else 0
      split_ifs with hn1
      · -- n + 1 = 1, so n = 0. Goal: coeff (n+1) + (1 - coeff 1 prev') = 1.
        -- With n = 0: coeff 1 + (1 - coeff 1) = 1.
        have hn : n = 0 := by omega
        subst hn
        ring
      · -- n + 1 ≠ 1. Goal: coeff (n+1) + (-coeff (n+1)) = 0.
        ring

open PowerSeries in
/-- **Main result** (T-IV-5-002, T-IV-5-003 core): `compInverse f` is a true
right compositional inverse of `f`, i.e. `PowerSeries.subst (compInverse f) f = X`,
whenever `constantCoeff f = 0` and `coeff 1 f = 1`. -/
theorem subst_compInverse_eq_X (f : PowerSeries R)
    (h0 : @PowerSeries.constantCoeff R _ f = 0) (h1 : PowerSeries.coeff 1 f = 1) :
    PowerSeries.subst (compInverse f) f = PowerSeries.X := by
  ext k
  -- Show coeff k of both sides are equal.
  -- For k = 0: handle the constant coefficient directly.
  -- For k ≥ 1: use stabilization `compInvTrunc f k` ↔ `compInverse f` and invariant.
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    -- coeff 0 (subst (compInverse f) f) = constantCoeff f = 0 = coeff 0 X.
    have hmv : @PowerSeries.constantCoeff R _ (PowerSeries.subst (compInverse f) f) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (compInverse_constantCoeff f) f h0
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [hmv]
    rw [PowerSeries.coeff_zero_X]
  · -- k ≥ 1.
    -- coeff k (subst (compInverse f) f) = coeff k (subst (compInvTrunc f k) f)
    -- since compInverse f and compInvTrunc f k agree up to degree k.
    have hstab : ∀ j ≤ k,
        PowerSeries.coeff j (compInverse f) =
          PowerSeries.coeff j (compInvTrunc f k) := by
      intro j hj
      rw [show PowerSeries.coeff j (compInverse f) = compInvCoeff f j from by
        simp [compInverse]]
      rw [coeff_compInvTrunc_of_le f k j hj]
    rw [coeff_subst_eq_of_coeff_eq f (compInverse f) (compInvTrunc f k)
          (compInverse_constantCoeff f) (compInvTrunc_constantCoeff f k)
          k hstab k le_rfl]
    rw [compInvTrunc_subst_coeff_eq f h0 h1 k k le_rfl]
    -- coeff k X = if k = 1 then 1 else 0.
    rw [PowerSeries.coeff_X]

/-! ### Compositional inverse for unit leading coefficient

For `f : PowerSeries R` with `constantCoeff f = 0` and `coeff 1 f = u`
where `u` is a unit, we construct a compositional inverse by reducing
to the `coeff 1 = 1` case via scaling.

Concretely, let `v = u⁻¹` (the inverse of `u` as a unit of `R`). Then
`f̃ := v • f` has `coeff 1 f̃ = v * u = 1`. Applying the existing
`compInverse` gives `g̃` with `subst g̃ f̃ = X`. By `subst_smul` this
means `subst g̃ f = u • X`. To land on `X` rather than `u • X`, we
reparametrise: `g := subst (v • X) g̃`. Then
`subst g f = subst (v • X) (subst g̃ f) = subst (v • X) (u • X) = u • (v • X) = X`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2 (b) and
the unit-leading-coefficient variant used for `[m] : F → F` when `m`
is a unit (T-IV-2-008). -/

open PowerSeries in
/-- The rescaled series `v • f` has zero constant coefficient whenever `f` does. -/
private theorem scaled_constantCoeff_zero (f : PowerSeries R) (v : R)
    (h0 : @PowerSeries.constantCoeff R _ f = 0) :
    @PowerSeries.constantCoeff R _ (v • f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change (v • PowerSeries.coeff 0 f) = 0
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, smul_zero]

open PowerSeries in
/-- The rescaled series `v • f` has linear coefficient `v * coeff 1 f`. -/
private theorem scaled_coeff_one (f : PowerSeries R) (v : R) :
    PowerSeries.coeff 1 (v • f) = v * PowerSeries.coeff 1 f := by
  change (v • PowerSeries.coeff 1 f) = v * PowerSeries.coeff 1 f
  rw [smul_eq_mul]

open PowerSeries in
/-- `v • X` has zero constant coefficient (so it admits substitution). -/
private theorem smul_X_constantCoeff_zero (v : R) :
    @PowerSeries.constantCoeff R _ ((v • PowerSeries.X : PowerSeries R)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change (v • (PowerSeries.coeff 0 PowerSeries.X : R)) = 0
  rw [PowerSeries.coeff_zero_X, smul_zero]

end CompInverseProof

/-- **Generalised compositional inverse** for power series with *unit*
leading coefficient.

Given `f : PowerSeries R` with `constantCoeff f = 0` and `coeff 1 f = u`
where `u` is a unit of `R`, this returns a right compositional inverse
`g` characterised by `subst g f = X` (see
`subst_compInverseOfUnit_eq_X`).

The construction reduces to the monic case via scaling: let
`v := (hu.unit)⁻¹`. Then `f̃ := v • f` is *monic* (linear coefficient
`1`), `g̃ := compInverse f̃` inverts `f̃`, and
`g := subst (v • X) g̃` inverts `f` itself.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2 —
compositional inverse when the leading coefficient is a unit (needed
for T-IV-2-008: `[m]` is an iso when `m ∈ R*`). -/
noncomputable def compInverseOfUnit (f : PowerSeries R) (u : R) (hu : IsUnit u) :
    PowerSeries R :=
  let v : R := ((hu.unit⁻¹ : Rˣ) : R)
  PowerSeries.subst ((v • PowerSeries.X : PowerSeries R)) (compInverse (v • f))

open PowerSeries in
/-- The constant coefficient of `compInverseOfUnit f u hu` is zero. -/
@[simp]
theorem compInverseOfUnit_constantCoeff (f : PowerSeries R) (u : R) (hu : IsUnit u) :
    @PowerSeries.constantCoeff R _ (compInverseOfUnit f u hu) = 0 := by
  unfold compInverseOfUnit
  set v : R := ((hu.unit⁻¹ : Rˣ) : R)
  -- compInverseOfUnit is a substitution into `compInverse (v • f)`, which has
  -- zero constant coefficient; so does the outer substitution.
  exact PowerSeries.constantCoeff_subst_eq_zero
    (smul_X_constantCoeff_zero v) _ (compInverse_constantCoeff _)

open PowerSeries in
/-- `compInverseOfUnit f u hu` admits substitution. -/
theorem compInverseOfUnit_hasSubst (f : PowerSeries R) (u : R) (hu : IsUnit u) :
    PowerSeries.HasSubst (compInverseOfUnit f u hu) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (compInverseOfUnit_constantCoeff f u hu)

open PowerSeries in
/-- **Compositional inverse identity** (unit case): for `f : PowerSeries R`
with `constantCoeff f = 0` and `coeff 1 f = u` (a unit),
`subst (compInverseOfUnit f u hu) f = X`.

This is the generalisation of `subst_compInverse_eq_X` from the monic case
(`coeff 1 f = 1`) to the unit case (`coeff 1 f = u` for any unit `u`). -/
theorem subst_compInverseOfUnit_eq_X (f : PowerSeries R) (u : R) (hu : IsUnit u)
    (h0 : @PowerSeries.constantCoeff R _ f = 0)
    (h1 : PowerSeries.coeff 1 f = u) :
    PowerSeries.subst (compInverseOfUnit f u hu) f = PowerSeries.X := by
  -- Strategy: unfold, use subst_comp_subst_apply, subst_smul, subst_X, and
  -- the monic-case theorem `subst_compInverse_eq_X` on `v • f`.
  unfold compInverseOfUnit
  set v : R := ((hu.unit⁻¹ : Rˣ) : R) with hv_def
  -- Key facts about v: v * u = 1 and u * v = 1.
  have hvu : v * u = 1 := by
    rw [hv_def]
    exact hu.val_inv_mul
  have huv : u * v = 1 := by
    rw [hv_def]
    exact hu.mul_val_inv
  -- Auxiliary: v • f has zero constant coefficient and linear coefficient 1.
  have hvf_const : @PowerSeries.constantCoeff R _ (v • f) = 0 :=
    scaled_constantCoeff_zero f v h0
  have hvf_one : PowerSeries.coeff 1 (v • f) = 1 := by
    rw [scaled_coeff_one, h1, hvu]
  -- Apply the monic case to f̃ := v • f.
  have hmonic : PowerSeries.subst (compInverse (v • f)) (v • f) = PowerSeries.X :=
    subst_compInverse_eq_X (v • f) hvf_const hvf_one
  -- Substitution of the compositional inverse `g̃ := compInverse (v • f)` admits substitution.
  have hsubst_g : PowerSeries.HasSubst (compInverse (v • f)) :=
    compInverse_hasSubst _
  -- From hmonic + subst_smul: v • subst g̃ f = X, i.e. subst g̃ f = u • X.
  have hsubst_smul : PowerSeries.subst (compInverse (v • f)) (v • f) =
      v • PowerSeries.subst (compInverse (v • f)) f :=
    PowerSeries.subst_smul hsubst_g v f
  have hkey : v • PowerSeries.subst (compInverse (v • f)) f = PowerSeries.X := by
    rw [← hsubst_smul]; exact hmonic
  -- Hence subst g̃ f = u • X via u • (v • y) = (u*v) • y = 1 • y = y.
  have h_gf : PowerSeries.subst (compInverse (v • f)) f = u • PowerSeries.X := by
    have hscale : u • (v • PowerSeries.subst (compInverse (v • f)) f) = u • PowerSeries.X := by
      rw [hkey]
    -- u • (v • y) = (u * v) • y = 1 • y = y.
    have heq : u • (v • PowerSeries.subst (compInverse (v • f)) f) =
        PowerSeries.subst (compInverse (v • f)) f := by
      have h1 : u • (v • PowerSeries.subst (compInverse (v • f)) f) =
          (u * v) • PowerSeries.subst (compInverse (v • f)) f :=
        (mul_smul u v _).symm
      rw [h1, huv]
      exact one_smul R _
    rw [heq] at hscale
    exact hscale
  -- Now compute: subst (subst (v • X) g̃) f = subst (v • X) (subst g̃ f).
  -- subst_comp_subst_apply ha hb f : subst b (subst a f) = subst (subst b a) f.
  -- Take a := g̃, b := v • X, so that the RHS is exactly our current goal's LHS.
  have hsX : PowerSeries.HasSubst ((v • PowerSeries.X : PowerSeries R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (smul_X_constantCoeff_zero v)
  rw [← PowerSeries.subst_comp_subst_apply hsubst_g hsX f]
  -- Goal: subst (v • X) (subst g̃ f) = X.
  rw [h_gf]
  -- Goal: subst (v • X) (u • X) = X.
  rw [PowerSeries.subst_smul hsX u PowerSeries.X]
  -- Goal: u • subst (v • X) X = X.
  rw [PowerSeries.subst_X hsX]
  -- Goal: u • (v • X) = X.
  -- Use calc / explicit term to avoid rewrite pattern matching trouble.
  calc u • (v • (PowerSeries.X : PowerSeries R))
      = (u * v) • (PowerSeries.X : PowerSeries R) := (mul_smul u v _).symm
    _ = (1 : R) • (PowerSeries.X : PowerSeries R) := by rw [huv]
    _ = PowerSeries.X := one_smul R _

open PowerSeries in
/-- The linear coefficient of `compInverseOfUnit f u hu` is `(hu.unit)⁻¹`.

This follows from the construction
`compInverseOfUnit f u hu = subst (v • X) (compInverse (v • f))` (with
`v = (hu.unit)⁻¹`): substituting `v • X` is the rescale by `v`, and
`coeff 1 (compInverse _) = 1` always (by `compInverse_coeff_one`), so
`coeff 1 (rescale v _) = v * 1 = v`. -/
@[simp]
theorem compInverseOfUnit_coeff_one (f : PowerSeries R) (u : R) (hu : IsUnit u) :
    PowerSeries.coeff 1 (compInverseOfUnit f u hu) = ((hu.unit⁻¹ : Rˣ) : R) := by
  unfold compInverseOfUnit
  set v : R := ((hu.unit⁻¹ : Rˣ) : R) with hv_def
  -- subst (v • X) g = rescale v g.
  rw [← PowerSeries.rescale_eq_subst]
  -- coeff 1 (rescale v g) = v^1 * coeff 1 g = v * coeff 1 g.
  rw [PowerSeries.coeff_rescale]
  -- Goal: v ^ 1 * coeff 1 (compInverse (v • f)) = v.
  rw [pow_one, compInverse_coeff_one, mul_one]

/-- The **formal exponential** of a formal group `F` over a ring with a
`ℚ`-module structure.

Defined as the compositional inverse of `log_F`, via `compInverse`.
The full inverse identity `log_F ∘ exp_F = X` (Silverman IV.5.2) is future
work — this file only establishes the definition and basic coefficient
properties.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.5. -/
noncomputable def FormalGroup.exp (F : FormalGroup R) [Module ℚ R] :
    PowerSeries R :=
  compInverse F.log

/-- The constant coefficient of `exp F` is zero. -/
@[simp]
theorem FormalGroup.exp_coeff_zero (F : FormalGroup R) [Module ℚ R] :
    PowerSeries.coeff 0 F.exp = 0 := by
  simp [FormalGroup.exp]

/-- `constantCoeff (exp F) = 0`. -/
@[simp]
theorem FormalGroup.exp_constantCoeff (F : FormalGroup R) [Module ℚ R] :
    @PowerSeries.constantCoeff R _ F.exp = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact F.exp_coeff_zero

/-! ### Silverman IV.5 corollaries

These finish the "structural" tickets T-IV-5-004, -005, -006. In our framework
commutativity is axiomatic (baked into the `FormalGroup` structure), so
T-IV-5-004 reduces to `F.comm`. The `b_n` bound (IV.5.4) translates to the
identity `n • log_F.coeff n = ω_F.coeff (n-1)` (no integer division since the
rational scalar cancels with `n`). -/

/-- **Silverman IV.5.3**: Every formal group is commutative. In our framework
this is axiomatic (built into the `FormalGroup` structure); over torsion-free
ℤ-algebras it's the classical non-trivial statement.

The exposed form is the bivariate identity `F(X, Y) = F(Y, X)`. -/
theorem FormalGroup.commutative (F : FormalGroup R) :
    MvPowerSeries.subst
        (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R)
        F.toSeries = F.toSeries :=
  F.comm

/-- **Silverman IV.5.3** under the torsion-free hypothesis — same as
`FormalGroup.commutative` in our framework (the hypothesis is not needed
because commutativity is axiomatic). -/
theorem FormalGroup.commutative_of_torsion_free (F : FormalGroup R)
    [NoZeroSMulDivisors ℤ R] :
    MvPowerSeries.subst
        (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R)
        F.toSeries = F.toSeries :=
  F.commutative

/-- **Silverman IV.5.4 (coefficient identity)**: for `n ≥ 1`,
`n • log_F.coeff n = ω_F.coeff (n - 1)`.

This is the `ℚ`-module-level identity that, after multiplying by `(n : ℚ)⁻¹`,
recovers the explicit formula `log_F.coeff n = (n : ℚ)⁻¹ • ω_F.coeff (n-1)`
(which is the content of `log_coeff_succ`). Over a torsion-free `ℤ`-algebra
it shows `n · log_F.coeff n` lies in the image of `ω_F`, which is the
`ℤ[a_i]`-containment stated in Silverman. -/
theorem FormalGroup.log_coeff_succ_nsmul (F : FormalGroup R) [Module ℚ R] (n : ℕ) :
    (n + 1) • PowerSeries.coeff (n + 1) F.log =
      PowerSeries.coeff n F.normalizedDifferential.toSeries := by
  rw [F.log_coeff_succ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  rw [show ((n + 1 : ℕ) : ℚ) * ((n + 1 : ℚ)⁻¹) = 1 by
    push_cast; field_simp]
  rw [one_smul]

/-! ### Silverman IV.5.2: `log_F` is a homomorphism `F → Ĝ_a`

The target identity: `log_F(F(X, Y)) = log_F(X) + log_F(Y)` as bivariate
power series. Concretely, the `preserves_add` axiom of a
`FormalGroupHom F (additiveFormalGroup R)`:
```
PowerSeries.subst F.toSeries F.log =
  MvPowerSeries.subst ![subst (X 0) F.log, subst (X 1) F.log]
    (additiveFormalGroup R).toSeries
```

Because `(additiveFormalGroup R).toSeries = X 0 + X 1`, this unfolds to
```
PowerSeries.subst F.toSeries F.log =
  PowerSeries.subst (X 0) F.log + PowerSeries.subst (X 1) F.log
```
(the RHS being the formal sum of two univariate substitutions, viewed as
bivariate series).

**Proof strategy (Silverman IV.5.2)**: differentiate both sides with respect
to `X`. The derivative of the LHS is `ω_F(F(X, Y)) · F_X(X, Y)`; by the
translation-invariance of `ω_F` (Silverman Prop. IV.4.2), this equals
`ω_F(X)`, which matches the derivative of the RHS. Hence the two bivariate
series differ by a series in `Y` alone. Setting `X = 0` and using
`log_F(F(0, Y)) = log_F(Y)` (from `F.runit`) plus `log_F(0) = 0` shows the
difference vanishes.

**Status**: this direction (LHS = RHS) requires the translation-invariance
`ω_F(F(T, S)) · F_T(T, S) = ω_F(T)`, which has not yet been ported from
Silverman IV.4.2. See the progress log in the ticket
`T-IV-5-003-log-iso-Ga.md`.

We record here the target statement as a `Prop` plus the achievable
intermediate lemmas (constant coefficient, linear coefficients at `(1, 0)`
and `(0, 1)`). The full statement is left as future work. -/

/-- The `preserves_add` identity for `log_F`, stated as a `Prop`:
`log_F(F(X, Y)) = log_F(X) + log_F(Y)` in `MvPowerSeries (Fin 2) R`.

Concretely the equation reads:
```
PowerSeries.subst F.toSeries F.log =
  PowerSeries.subst (MvPowerSeries.X 0) F.log +
    PowerSeries.subst (MvPowerSeries.X 1) F.log
```

This is the `preserves_add` axiom of a would-be
`FormalGroupHom F (additiveFormalGroup R)`. See `T-IV-5-003`. -/
def FormalGroup.LogPreservesAdd (F : FormalGroup R) [Module ℚ R] : Prop :=
  PowerSeries.subst F.toSeries F.log =
    PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log

/-! #### Setup: substitutions of `F.log` as bivariate series. -/

/-- `subst F.toSeries F.log` (the LHS of `LogPreservesAdd`) has zero constant
coefficient. This is the bivariate-substitution constant coefficient computation.

In particular, evaluated at `(0, 0)`, `log_F(F(0, 0)) = log_F(0) = 0`. -/
theorem FormalGroup.constantCoeff_log_subst (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.constantCoeff
        ((PowerSeries.subst F.toSeries F.log : MvPowerSeries (Fin 2) R)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero
    (HasseWeil.FG.constantCoeff_FG_toSeries F) F.log F.log_constantCoeff

/-- The RHS of `LogPreservesAdd`, expanded: `subst (X 0) log + subst (X 1) log`
has zero constant coefficient. Combined with
`constantCoeff_log_subst`, this establishes the zeroth-coefficient case of
`LogPreservesAdd`. -/
theorem FormalGroup.constantCoeff_log_subst_X_add (F : FormalGroup R) [Module ℚ R] :
    @MvPowerSeries.constantCoeff (Fin 2) R _
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log) = 0 := by
  rw [map_add]
  rw [PowerSeries.constantCoeff_subst_eq_zero (by simp) F.log F.log_constantCoeff]
  rw [PowerSeries.constantCoeff_subst_eq_zero (by simp) F.log F.log_constantCoeff]
  simp

/-- **Constant-coefficient case of `LogPreservesAdd`**: the constant coefficient
(i.e., the value at `(0, 0)`) of both sides of `LogPreservesAdd F` agree.

This is a necessary condition for `LogPreservesAdd F`. -/
theorem FormalGroup.logPreservesAdd_constantCoeff (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.constantCoeff
        ((PowerSeries.subst F.toSeries F.log : MvPowerSeries (Fin 2) R)) =
      @MvPowerSeries.constantCoeff (Fin 2) R _
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log) := by
  rw [F.constantCoeff_log_subst, F.constantCoeff_log_subst_X_add]

/-! #### The case `F = Ĝ_a`: the trivial case of `LogPreservesAdd`

For the additive formal group `Ĝ_a(X, Y) = X + Y`, the logarithm is the
identity `log_F(T) = T` (since `ω_F(T) = 1`, so `log_F(T) = T + 0 + ...`).
This makes the `preserves_add` identity immediate. -/

/-- For the additive formal group `Ĝ_a(X, Y) = X + Y`, the partial derivative
`F_X(0, T)` is the constant `1`. Concretely `dX_at_zero` has coefficient `1` at
degree `0` and `0` elsewhere.

Helper for `FormalGroup.log_additiveFormalGroup`. -/
private theorem FormalGroup.dX_at_zero_additiveFormalGroup [Module ℚ R] :
    (additiveFormalGroup R).dX_at_zero = 1 := by
  ext k
  rw [FormalGroup.dX_at_zero, PowerSeries.coeff_mk]
  change MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) k)
    ((MvPowerSeries.X 0 + MvPowerSeries.X 1 :
      MvPowerSeries (Fin 2) R)) = _
  rw [map_add]
  rw [show (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) =
    MvPowerSeries.X 0 ^ 1 from (pow_one _).symm]
  rw [show (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) =
    MvPowerSeries.X 1 ^ 1 from (pow_one _).symm]
  rw [MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X_pow]
  match k with
  | 0 =>
    -- The LHS: (if pos then 1 else 0) + (if single 0 1 = single 1 1 then 1 else 0)
    -- = 1 + 0 = 1.
    simp only [Finsupp.single_zero, add_zero, if_true]
    rw [if_neg (by
      intro h
      have := DFunLike.congr_fun h 0
      simp [Finsupp.single_eq_same] at this)]
    rw [add_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp
  | k + 1 =>
    rw [if_neg (by
      intro h
      have := DFunLike.congr_fun h 1
      simp [Finsupp.add_apply, Finsupp.single_eq_same] at this)]
    rw [if_neg (by
      intro h
      have h0 := DFunLike.congr_fun h 0
      simp [Finsupp.add_apply, Finsupp.single_eq_same] at h0)]
    rw [zero_add, PowerSeries.coeff_one, if_neg (by omega : k + 1 ≠ 0)]

/-- For the additive formal group, the normalized differential `ω_{Ĝ_a}` is the
constant series `1`. This follows from `dX_at_zero = 1` (see
`FormalGroup.dX_at_zero_additiveFormalGroup`) together with
`dX_at_zero_mul_invariantDiff`.

Helper for `FormalGroup.log_additiveFormalGroup`. -/
private theorem FormalGroup.normalizedDifferential_toSeries_additiveFormalGroup [Module ℚ R] :
    (additiveFormalGroup R).normalizedDifferential.toSeries = 1 := by
  change (additiveFormalGroup R).invariantDiff = 1
  have h1 : (additiveFormalGroup R).dX_at_zero * (additiveFormalGroup R).invariantDiff = 1 :=
    (additiveFormalGroup R).dX_at_zero_mul_invariantDiff
  rw [FormalGroup.dX_at_zero_additiveFormalGroup] at h1
  rw [show ((1 : PowerSeries R) * (additiveFormalGroup R).invariantDiff) =
    (additiveFormalGroup R).invariantDiff from one_mul _] at h1
  exact h1

/-- For the additive formal group, `log = X`. Since `ω_F = 1`, we have
`log_F(T) = T + 0 + ... = T`. -/
theorem FormalGroup.log_additiveFormalGroup [Module ℚ R] :
    (additiveFormalGroup R).log = PowerSeries.X := by
  -- We show `coeff n` agreement for all n. The n = 1 case gives `1`,
  -- all other cases give `0`.
  ext n
  match n with
  | 0 =>
    rw [FormalGroup.log_coeff_zero]
    rw [PowerSeries.coeff_zero_X]
  | 1 =>
    rw [FormalGroup.log_coeff_one]
    rw [PowerSeries.coeff_one_X]
  | n + 2 =>
    -- coeff (n+2) log = ((n+2)⁻¹) • coeff (n+1) ω_F (from log_coeff_succ for Ĝ_a).
    -- For Ĝ_a, coeff k ω_F = [k = 0], so coeff (n+1) ω_F = 0 since n + 1 ≥ 1.
    rw [show (n + 2 : ℕ) = ((n + 1) + 1 : ℕ) from rfl]
    rw [FormalGroup.log_coeff_succ (additiveFormalGroup R) (n + 1)]
    -- For Ĝ_a, ω_F = 1 (see `normalizedDifferential_toSeries_additiveFormalGroup`),
    -- so its coefficient at `n + 1 ≥ 1` is `0`.
    rw [FormalGroup.normalizedDifferential_toSeries_additiveFormalGroup]
    -- Goal: ((n+2)⁻¹ : ℚ) • coeff (n+1) (1 : PowerSeries R) = coeff (n+2) X
    rw [PowerSeries.coeff_one, if_neg (by omega : n + 1 ≠ 0), smul_zero,
      PowerSeries.coeff_X, if_neg (by omega : n + 1 + 1 ≠ 1)]

/-- **Silverman IV.5.2 for `Ĝ_a`**: the additive formal group's log is
the identity, and as a trivial consequence, it preserves addition. -/
theorem FormalGroup.additiveFormalGroup_logPreservesAdd [Module ℚ R] :
    (additiveFormalGroup R).LogPreservesAdd := by
  unfold FormalGroup.LogPreservesAdd
  rw [FormalGroup.log_additiveFormalGroup]
  -- Goal: subst (additiveFormalGroup R).toSeries X =
  --       subst (X 0) X + subst (X 1) X
  have h_F : PowerSeries.HasSubst
      ((additiveFormalGroup R).toSeries : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero
      (HasseWeil.FG.constantCoeff_FG_toSeries _)
  have h_X0 : PowerSeries.HasSubst
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h_X1 : PowerSeries.HasSubst
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.subst_X h_F, PowerSeries.subst_X h_X0, PowerSeries.subst_X h_X1]
  -- Goal: (additiveFormalGroup R).toSeries = X 0 + X 1. This is rfl by definition.
  rfl

/-! #### The general case: `LogPreservesAdd F` via Silverman IV.4.2

The proof follows Silverman IV.5: differentiate both sides of
`log_F(F(X, Y)) = log_F(X) + log_F(Y)` with respect to `X`. The LHS derivative
(chain rule + IV.4.2 translation invariance) equals `ω_F(X)`; the RHS
derivative is `ω_F(X)` directly. Hence both sides have the same partial
derivative in `X`. Combined with agreement at `X = 0` (via the right unit
`F(0, Y) = Y` and `log_F(0) = 0`), they are equal because `Module ℚ R`
makes `R` torsion-free. -/

/-- **Key derivative identity**: `pderiv () F.log = F.invariantDiff`
(both viewed as `MvPowerSeries Unit R = PowerSeries R`).

This is the formal Silverman IV.5 definition of `log_F`: it is the unique
power series with zero constant term whose derivative equals the normalized
invariant differential. -/
theorem FormalGroup.pderiv_log (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.pderiv () F.log = F.invariantDiff := by
  ext n
  -- PowerSeries.coeff n on LHS = MvPowerSeries.coeff (single () n).
  change MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderiv () F.log) =
      PowerSeries.coeff n F.invariantDiff
  rw [MvPowerSeries.coeff_pderiv]
  -- Compute (single () n) () = n and (single () n) + (single () 1) = single () (n+1).
  have h1 : (Finsupp.single () n : Unit →₀ ℕ) () = n := by simp
  have h2 : (Finsupp.single () n : Unit →₀ ℕ) + Finsupp.single () 1 =
      Finsupp.single () (n + 1) := by
    rw [← Finsupp.single_add]
  rw [h1, h2]
  -- Goal: (n + 1) • MvPowerSeries.coeff (single () (n+1)) F.log = coeff n F.invariantDiff.
  change (n + 1) • PowerSeries.coeff (n + 1) F.log = PowerSeries.coeff n F.invariantDiff
  rw [FormalGroup.log_coeff_succ]
  -- `ω_F = F.invariantDiff` by definition of `normalizedDifferential`.
  change (n + 1) • (((n + 1 : ℚ)⁻¹) • PowerSeries.coeff n F.invariantDiff) =
      PowerSeries.coeff n F.invariantDiff
  -- Cancel the (n+1) scalar: (n+1 : ℕ) • x = (n+1 : ℚ) • x.
  rw [← Nat.cast_smul_eq_nsmul ℚ (n + 1), smul_smul,
    show ((n + 1 : ℕ) : ℚ) * ((n + 1 : ℚ)⁻¹) = 1 by push_cast; field_simp]
  exact one_smul ℚ _

/-! #### Chain rule for `PowerSeries.subst` via `MvPowerSeries.pderiv`

For `f : PowerSeries R` and `a : MvPowerSeries τ R` with `PowerSeries.HasSubst a`,
`pderiv t (PowerSeries.subst a f) = pderiv t a * PowerSeries.subst a (pderiv () f)`.

This is the specialization of the multivariate chain rule
`MvPowerSeries.pderiv_subst` to `σ = Unit`. -/

/-- Chain rule for `PowerSeries.subst`: for `f : PowerSeries R` and
`a : MvPowerSeries τ R` with `PowerSeries.HasSubst a`,
`pderiv t (subst a f) = pderiv t a * subst a (pderiv () f)`. -/
private theorem pderiv_PowerSeries_subst {τ : Type*}
    (t : τ) {a : MvPowerSeries τ R} (ha : PowerSeries.HasSubst a)
    (f : PowerSeries R) :
    MvPowerSeries.pderiv t (PowerSeries.subst a f) =
      MvPowerSeries.pderiv t a * PowerSeries.subst a (MvPowerSeries.pderiv () f) := by
  rw [PowerSeries.subst_def]
  rw [MvPowerSeries.pderiv_subst t ha.const f]
  rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
  rfl

/-! #### Uniqueness: a two-variable series is determined by its derivative in
variable 0 and its value at `X 0 = 0`. -/

/-- Auxiliary: if `h : MvPowerSeries (Fin 2) R` has zero derivative in variable
`0` (over a `Module ℚ R`), then all coefficients with positive 0-degree vanish.
-/
private theorem coeff_zero_of_pderiv_zero_fin2 [Module ℚ R]
    (h : MvPowerSeries (Fin 2) R) (hd : MvPowerSeries.pderiv 0 h = 0)
    (e : Fin 2 →₀ ℕ) (he : e 0 ≠ 0) :
    MvPowerSeries.coeff e h = 0 := by
  haveI : IsAddTorsionFree R := IsAddTorsionFree.of_module_rat R
  -- Obtain a : ℕ with e 0 = a + 1.
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero he
  -- Let d = e - single 0 1, so that d + single 0 1 = e and d 0 = a.
  set d : Fin 2 →₀ ℕ := e - Finsupp.single (0 : Fin 2) 1 with hd_def
  have hle : Finsupp.single (0 : Fin 2) 1 ≤ e := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [Finsupp.single_apply, if_pos rfl, ha]
      exact Nat.succ_pos a
    · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      exact Nat.zero_le _
  have hd_sum : d + Finsupp.single (0 : Fin 2) 1 = e := by
    rw [hd_def, tsub_add_cancel_of_le hle]
  have hd0 : d 0 = a := by
    have h1 : d 0 = e 0 - (Finsupp.single (0 : Fin 2) 1) 0 := by
      rw [hd_def]; simp
    rw [h1, ha]; simp
  have key : (d 0 + 1 : ℕ) •
      MvPowerSeries.coeff (d + Finsupp.single (0 : Fin 2) 1) h = 0 := by
    have h_c := congr_arg (MvPowerSeries.coeff d) hd
    rw [MvPowerSeries.coeff_pderiv] at h_c
    simpa using h_c
  rw [hd_sum] at key
  rw [hd0] at key
  -- Cancel the (a+1) nsmul using torsion-freeness.
  have hne : (a + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero a
  have := nsmul_right_injective hne
      (show (a + 1) • MvPowerSeries.coeff e h = (a + 1) • (0 : R) by rw [smul_zero]; exact key)
  exact this

/-- If `h : MvPowerSeries (Fin 2) R` has zero derivative in variable 0 and
zero coefficient at every `(0, b)`, then `h = 0`. -/
private theorem eq_zero_of_pderiv_zero_and_const_zero [Module ℚ R]
    (h : MvPowerSeries (Fin 2) R) (hd : MvPowerSeries.pderiv 0 h = 0)
    (hc : ∀ b : ℕ, MvPowerSeries.coeff
        (Finsupp.single (1 : Fin 2) b) h = 0) :
    h = 0 := by
  ext e
  rw [MvPowerSeries.coeff_zero]
  -- Split on whether e 0 = 0 or not.
  by_cases h0 : e 0 = 0
  · -- e 0 = 0: e = single 1 (e 1).
    have he : e = Finsupp.single (1 : Fin 2) (e 1) := by
      ext i
      fin_cases i
      · simp [h0]
      · simp
    rw [he]
    exact hc (e 1)
  · -- e 0 ≥ 1.
    exact coeff_zero_of_pderiv_zero_fin2 h hd e h0

/-! #### The main proof

The proof proceeds in three steps:

* `pderiv_LogPreservesAdd_LHS`: the derivative of the LHS via chain rule and
  IV.4.2 equals `subst (X 0) F.invariantDiff`.
* `pderiv_LogPreservesAdd_RHS`: the derivative of the RHS equals
  `subst (X 0) F.invariantDiff`.
* `FormalGroup.logPreservesAdd_subst_zero`: substituting `X 0 ↦ 0` on both
  sides gives the same bivariate power series `PowerSeries.subst (X 1) F.log`.
* Combine with the uniqueness lemma. -/

/-- The derivative of the LHS `subst F.toSeries F.log` in variable `0`:
  `pderiv 0 (subst F.toSeries F.log) = subst (X 0) F.invariantDiff`. -/
private theorem pderiv_LogPreservesAdd_LHS (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.pderiv 0
        ((PowerSeries.subst F.toSeries F.log) : MvPowerSeries (Fin 2) R) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
        F.invariantDiff := by
  have hF_subst : PowerSeries.HasSubst (F.toSeries : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (HasseWeil.FG.constantCoeff_FG_toSeries F)
  rw [pderiv_PowerSeries_subst 0 hF_subst F.log, F.pderiv_log]
  -- Goal: pderiv 0 F.toSeries * subst F.toSeries F.invariantDiff = subst (X 0) F.invariantDiff.
  -- By IV.4.2: subst F.toSeries F.invariantDiff * pderiv 0 F.toSeries
  --          = subst (X 0) F.invariantDiff.
  rw [mul_comm]
  exact F.invariantDiff_translation

/-- The derivative of the RHS `subst (X 0) F.log + subst (X 1) F.log` in
variable `0`: `pderiv 0 (...) = subst (X 0) F.invariantDiff`. -/
private theorem pderiv_LogPreservesAdd_RHS (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.pderiv 0
        ((PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log)) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
        F.invariantDiff := by
  have hX0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [MvPowerSeries.pderiv_add]
  rw [pderiv_PowerSeries_subst 0 hX0 F.log, pderiv_PowerSeries_subst 0 hX1 F.log]
  rw [F.pderiv_log]
  -- Simplify pderiv 0 (X 0) = 1 and pderiv 0 (X 1) = 0.
  rw [MvPowerSeries.pderiv_X_self 0]
  rw [MvPowerSeries.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  rw [one_mul, zero_mul, add_zero]

/-- Substituting `X 0 ↦ 0` in the LHS of `LogPreservesAdd`:
  `subst ![0, X 1] (subst F.toSeries F.log) = subst (X 1) F.log`. -/
private theorem subst_zero_LogPreservesAdd_LHS (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.subst
        (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R)
        (PowerSeries.subst F.toSeries F.log) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log := by
  have hF_subst : PowerSeries.HasSubst (F.toSeries : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (HasseWeil.FG.constantCoeff_FG_toSeries F)
  have h0X1 : MvPowerSeries.HasSubst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  -- subst ![0, X 1] ∘ subst F.toSeries f = subst (subst ![0, X 1] ∘ F.toSeries) f.
  -- For PowerSeries.subst this becomes subst (MvPowerSeries.subst ![0, X 1] F.toSeries) f.
  -- By F.runit, subst ![0, X 1] F.toSeries = X 1.
  rw [PowerSeries.subst_def]
  rw [MvPowerSeries.subst_comp_subst_apply hF_subst.const h0X1]
  have hX1_eq : (fun _ : Unit ↦ MvPowerSeries.subst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) F.toSeries) =
      (fun _ : Unit ↦ (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) := by
    funext _; exact F.runit
  rw [hX1_eq]
  rw [PowerSeries.subst_def]

/-- Helper: if `f : PowerSeries R` has zero constant coefficient, then
`PowerSeries.subst 0 f = 0` (as an element of `MvPowerSeries τ R`). -/
private theorem PowerSeries_subst_zero_of_constantCoeff_zero {τ : Type*}
    (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries τ R) f = 0 := by
  -- `subst 0 f` has the form `∑ coeff d f • 0^d = coeff 0 f • 1 = 0`.
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries τ R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  ext e
  rw [PowerSeries.coeff_subst h0 f e, MvPowerSeries.coeff_zero]
  -- Only d = 0 contributes, and `coeff 0 f = 0`.
  rw [finsum_eq_single _ 0
    (fun n hn ↦ by
      rw [zero_pow hn]
      rw [map_zero (MvPowerSeries.coeff e)]
      rw [smul_zero])]
  rw [pow_zero]
  have : PowerSeries.coeff 0 f = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hf
  rw [this, zero_smul]

/-- Substituting `X 0 ↦ 0` in the RHS of `LogPreservesAdd`:
  `subst ![0, X 1] (subst (X 0) F.log + subst (X 1) F.log) = subst (X 1) F.log`. -/
private theorem subst_zero_LogPreservesAdd_RHS (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.subst
        (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R)
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log := by
  have hX0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h0X1 : MvPowerSeries.HasSubst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  rw [MvPowerSeries.subst_add h0X1]
  -- Handle subst (X 0) F.log: becomes subst 0 F.log = 0 after substituting.
  have h_sub_X0 : MvPowerSeries.subst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R)
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log) = 0 := by
    rw [PowerSeries.subst_def]
    rw [MvPowerSeries.subst_comp_subst_apply hX0.const h0X1]
    have hconst : (fun _ : Unit ↦ MvPowerSeries.subst
        (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 2) R)
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)) =
        fun _ : Unit ↦ (0 : MvPowerSeries (Fin 2) R) := by
      funext _
      rw [MvPowerSeries.subst_X h0X1 0]
      rfl
    rw [hconst]
    change PowerSeries.subst (0 : MvPowerSeries (Fin 2) R) F.log = 0
    exact PowerSeries_subst_zero_of_constantCoeff_zero F.log F.log_constantCoeff
  rw [h_sub_X0, zero_add]
  -- Handle subst (X 1) F.log: becomes subst (X 1) F.log after substituting.
  rw [PowerSeries.subst_def]
  rw [MvPowerSeries.subst_comp_subst_apply hX1.const h0X1]
  have hX1_eq : (fun _ : Unit ↦ MvPowerSeries.subst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R)
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
      (fun _ : Unit ↦ (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) := by
    funext _
    rw [MvPowerSeries.subst_X h0X1 1]
    rfl
  rw [hX1_eq]

/-- Auxiliary: the coefficients of `subst ![0, X 1] h` at `single 1 b`
coincide with the coefficients of `h` at `single 1 b`. More explicitly,
if `g = subst ![0, X 1] h`, then `coeff (single 1 b) g = coeff (single 1 b) h`.

Proof strategy: substituting `X 0 ↦ 0` in the basis monomial `X 0^i X 1^j`
gives `0^i X 1^j`, which is `X 1^j` if `i = 0` and `0` otherwise. The
coefficient at `single 1 b` then picks out `coeff (0, b) h`. -/
private theorem coeff_subst_zero_X1_at_single_1 (h : MvPowerSeries (Fin 2) R) (b : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) b)
      (MvPowerSeries.subst (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) h) =
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) b) h := by
  have h0X1 : MvPowerSeries.HasSubst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  -- Substitute `X 0 ↦ 0, X 1 ↦ X 1`. First rewrite the LHS via coeff_subst.
  classical
  set a : Fin 2 → MvPowerSeries (Fin 2) R :=
    ![0, MvPowerSeries.X 1] with ha_def
  rw [MvPowerSeries.coeff_subst h0X1 h (Finsupp.single 1 b)]
  -- Goal: ∑ᶠ d, coeff d h • coeff (single 1 b) (d.prod (fun s e => (a s)^e))
  --          = coeff (single 1 b) h.
  -- Only d = single 1 b contributes; others give zero.
  rw [finsum_eq_single _ (Finsupp.single (1 : Fin 2) b)]
  · -- Case d = single 1 b: d.prod _ = (a 1)^b = (X 1)^b, coeff (single 1 b) ((X 1)^b) = 1.
    have hprod : (Finsupp.single (1 : Fin 2) b).prod
        (fun s e ↦ (a s) ^ e) =
        (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ b := by
      -- support of single 1 b is {1} if b ≠ 0, else ∅.
      by_cases hb : b = 0
      · subst hb
        simp [Finsupp.prod]
      · rw [Finsupp.prod_single_index (by simp)]
        rfl
    rw [hprod]
    -- coeff (single 1 b) ((X 1)^b) = 1.
    have hc : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) b)
        ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ b) = 1 := by
      rw [show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ b =
        MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) b) 1 by
        rw [MvPowerSeries.X_pow_eq]]
      exact MvPowerSeries.coeff_monomial_same _ _
    rw [hc, smul_eq_mul, mul_one]
  · -- For d ≠ single 1 b: the contribution is zero.
    intro d hd
    -- Two cases: d 0 ≠ 0 OR (d 0 = 0 AND d 1 ≠ b).
    by_cases h0 : d 0 = 0
    · -- d 0 = 0 but d ≠ single 1 b: so d 1 ≠ b.
      have hd1 : d 1 ≠ b := by
        intro h1
        apply hd
        ext i
        fin_cases i
        · change d 0 = (Finsupp.single (1 : Fin 2) b) 0
          rw [h0]; simp
        · change d 1 = (Finsupp.single (1 : Fin 2) b) 1
          rw [h1]; simp
      -- d.prod: support is subset of {0, 1}. Since d 0 = 0, support ⊆ {1}.
      -- d.prod = (a 1)^(d 1) = (X 1)^(d 1). Coefficient at (single 1 b) is 0 since d 1 ≠ b.
      have hprod : d.prod (fun s e ↦ (a s) ^ e) =
          (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ (d 1) := by
        -- d.prod over support. Support of d does not include 0 (since d 0 = 0).
        rw [Finsupp.prod]
        have : d.support ⊆ {1} := by
          intro i hi
          simp only [Finset.mem_singleton]
          fin_cases i
          · exact (Finsupp.mem_support_iff.mp hi h0).elim
          · rfl
        by_cases hb' : d 1 = 0
        · have : d.support = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro i hi
            have := this hi
            rw [Finset.mem_singleton] at this
            subst this
            exact Finsupp.mem_support_iff.mp hi hb'
          rw [this, Finset.prod_empty]
          rw [hb', pow_zero]
        · have : d.support = {1} := by
            apply Finset.Subset.antisymm this
            intro i hi
            rw [Finset.mem_singleton] at hi; subst hi
            exact Finsupp.mem_support_iff.mpr hb'
          rw [this, Finset.prod_singleton]
          rfl
      rw [hprod]
      have hc : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) b)
          ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ (d 1)) = 0 := by
        rw [show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ (d 1) =
            MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) (d 1)) 1 by
          rw [MvPowerSeries.X_pow_eq]]
        rw [MvPowerSeries.coeff_monomial_ne]
        intro heq
        have := DFunLike.congr_fun heq 1
        simp at this
        exact hd1 this.symm
      rw [hc, smul_zero]
    · -- d 0 ≠ 0: d.prod = 0.
      have hprod : d.prod (fun s e ↦ (a s) ^ e) = 0 := by
        rw [Finsupp.prod]
        -- 0 is in support since d 0 ≠ 0.
        have h0mem : (0 : Fin 2) ∈ d.support :=
          Finsupp.mem_support_iff.mpr h0
        rw [Finset.prod_eq_zero h0mem]
        simp [ha_def, zero_pow h0]
      rw [hprod, map_zero, smul_zero]

/-- The substitution `X 0 ↦ 0, X 1 ↦ X 1` (i.e. `![0, X 1]`) admits
substitution on `MvPowerSeries (Fin 2) R`, since both entries have zero
constant coefficient. -/
private theorem hasSubst_eval_zero_X1 :
    MvPowerSeries.HasSubst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s <;> simp

/-- **Step 1 of `LogPreservesAdd`**: the partial derivative in variable `0` of
the difference between the two sides of `LogPreservesAdd F` vanishes. Both sides
have the same `pderiv 0` (equal to `subst (X 0) F.invariantDiff`), via
`pderiv_LogPreservesAdd_LHS` and `pderiv_LogPreservesAdd_RHS`. -/
private theorem pderiv_zero_LogPreservesAdd_diff (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.pderiv 0
        (PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.log -
          (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
            PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log)) =
      0 := by
  rw [MvPowerSeries.pderiv_sub, pderiv_LogPreservesAdd_LHS F, pderiv_LogPreservesAdd_RHS F]
  exact sub_self _

/-- **Step 2 of `LogPreservesAdd`**: substituting `X 0 ↦ 0` in the difference
between the two sides of `LogPreservesAdd F` gives `0`. Each side reduces to
`subst (X 1) F.log` under this substitution, via `subst_zero_LogPreservesAdd_LHS`
and `subst_zero_LogPreservesAdd_RHS`. -/
private theorem subst_zero_X1_LogPreservesAdd_diff (F : FormalGroup R) [Module ℚ R] :
    MvPowerSeries.subst
        (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R)
        (PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.log -
          (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
            PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log)) =
      0 := by
  rw [← MvPowerSeries.substAlgHom_apply hasSubst_eval_zero_X1, map_sub,
    MvPowerSeries.substAlgHom_apply hasSubst_eval_zero_X1,
    MvPowerSeries.substAlgHom_apply hasSubst_eval_zero_X1,
    subst_zero_LogPreservesAdd_LHS F, subst_zero_LogPreservesAdd_RHS F]
  exact sub_self _

/-- **Uniqueness step**: a bivariate series `h` whose `pderiv 0` vanishes and
which becomes `0` after substituting `X 0 ↦ 0` is itself `0`. The substitution
hypothesis pins down every coefficient at `single 1 b` (via
`coeff_subst_zero_X1_at_single_1`), and `eq_zero_of_pderiv_zero_and_const_zero`
then concludes from the derivative hypothesis. -/
private theorem eq_zero_of_pderiv_zero_and_subst_zero_X1 [Module ℚ R]
    (h : MvPowerSeries (Fin 2) R) (hd : MvPowerSeries.pderiv 0 h = 0)
    (hsub : MvPowerSeries.subst
        (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) h = 0) :
    h = 0 := by
  apply eq_zero_of_pderiv_zero_and_const_zero h hd
  intro b
  have hcoeff := congr_arg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) b)) hsub
  rw [MvPowerSeries.coeff_zero] at hcoeff
  rw [← hcoeff]
  exact (coeff_subst_zero_X1_at_single_1 h b).symm

/-- **Silverman IV.5.2**: the formal logarithm preserves addition. -/
theorem FormalGroup.logPreservesAdd (F : FormalGroup R) [Module ℚ R] :
    F.LogPreservesAdd := by
  unfold FormalGroup.LogPreservesAdd
  -- Let `h` be the difference of the two sides; the goal is `h = 0`.
  set h : MvPowerSeries (Fin 2) R :=
    PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.log -
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log)
    with hh
  suffices h = 0 by rw [hh] at this; linear_combination this
  -- `pderiv 0 h = 0` (Step 1) and `subst (X 0 ↦ 0) h = 0` (Step 2) force `h = 0`.
  exact eq_zero_of_pderiv_zero_and_subst_zero_X1 h
    (hh ▸ pderiv_zero_LogPreservesAdd_diff F) (hh ▸ subst_zero_X1_LogPreservesAdd_diff F)

/-! #### Packaging `log_F` as a formal group homomorphism

Assuming `LogPreservesAdd F` (i.e., the target identity of Silverman IV.5.2),
we package `log_F` as a `FormalGroupHom F (additiveFormalGroup R)`.

The construction only requires the identity of `LogPreservesAdd` plus the
fact that `log_F` has zero constant coefficient (which is `log_coeff_zero`).
The `preserves_add` axiom of the homomorphism is an unfolding of the
`LogPreservesAdd` identity. -/

/-- Under the hypothesis `LogPreservesAdd F`, `log_F` extends to a formal
group homomorphism `F → Ĝ_a`. This is the packaging part of the
iso statement of Silverman IV.5.2; the hard work is the
`LogPreservesAdd F` identity itself (the `preserves_add` axiom). -/
noncomputable def FormalGroup.logHomOfLogPreservesAdd
    (F : FormalGroup R) [Module ℚ R]
    (hlog : F.LogPreservesAdd) :
    FormalGroupHom F (additiveFormalGroup R) where
  toSeries := F.log
  zero_const := F.log_constantCoeff
  preserves_add := by
    -- Unfold LogPreservesAdd: the identity is
    --   subst F.toSeries F.log = subst (X 0) F.log + subst (X 1) F.log.
    -- The target statement is:
    --   subst F.toSeries F.log = subst ![...] (additiveFormalGroup R).toSeries.
    -- (additiveFormalGroup R).toSeries = X 0 + X 1, and we unfold the
    -- MvPowerSeries.subst of a sum.
    rw [hlog]
    -- Now target: subst (X 0) F.log + subst (X 1) F.log
    --           = MvPowerSeries.subst ![subst (X 0) F.log, subst (X 1) F.log]
    --                (X 0 + X 1)
    have hpair : MvPowerSeries.HasSubst
        (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.log,
           PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) F.log] :
          Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;>
        (change MvPowerSeries.constantCoeff
            (PowerSeries.subst _ F.log) = 0;
          exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _ F.log_constantCoeff)
    change _ = MvPowerSeries.subst
      (![_, _] : Fin 2 → MvPowerSeries (Fin 2) R)
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R))
    rw [MvPowerSeries.subst_add hpair, MvPowerSeries.subst_X hpair 0,
      MvPowerSeries.subst_X hpair 1]
    -- Goal: subst (X 0) log + subst (X 1) log =
    --       ![subst (X 0) log, subst (X 1) log] 0 + ![subst (X 0) log, subst (X 1) log] 1
    rfl

@[simp]
theorem FormalGroup.logHomOfLogPreservesAdd_toSeries
    (F : FormalGroup R) [Module ℚ R] (hlog : F.LogPreservesAdd) :
    (F.logHomOfLogPreservesAdd hlog).toSeries = F.log := rfl

/-- **Silverman IV.5.2 corollary for `Ĝ_a`**: the identity as a formal
group homomorphism `Ĝ_a → Ĝ_a` (packaged via `logHomOfLogPreservesAdd`).
Follows from `additiveFormalGroup_logPreservesAdd`. -/
noncomputable def FormalGroup.additiveFormalGroup_logHom [Module ℚ R] :
    FormalGroupHom (additiveFormalGroup R) (additiveFormalGroup R) :=
  (additiveFormalGroup R).logHomOfLogPreservesAdd
    (FormalGroup.additiveFormalGroup_logPreservesAdd)

/-- **`log_F` as a `FormalGroupHom`** (Silverman IV.5.2 packaged).

For a formal group `F` over a `ℚ`-module `R`, `log_F : F → Ĝ_a` is a formal
group homomorphism. The underlying series is `F.log`, and the `preserves_add`
axiom is `F.logPreservesAdd`. -/
noncomputable def FormalGroup.logHom (F : FormalGroup R) [Module ℚ R] :
    FormalGroupHom F (additiveFormalGroup R) :=
  F.logHomOfLogPreservesAdd F.logPreservesAdd

@[simp]
theorem FormalGroup.logHom_toSeries (F : FormalGroup R) [Module ℚ R] :
    F.logHom.toSeries = F.log := rfl

end HasseWeil.FormalGroup

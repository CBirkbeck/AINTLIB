module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
public import BernoulliRegular.FLT37.PrimaryUnits.Part1

/-!
# Primary units of `𝓞 K⁺` (ticket FLT37c, scaffold)

For Vandiver Lemma 2 (primary unit decomposition), an element
`γ ∈ 𝓞 K⁺` is **primary** when it is congruent to a rational integer
modulo `𝔭⁺^p`, where `𝔭⁺` is the unique prime of `𝓞 K⁺` above `(p)`.
Equivalently (since `𝔭⁺·𝓞 K = 𝔭² = (ζ-1)^2`), this is
`γ ≡ a (mod (ζ-1)^{2p})` viewed in `𝓞 K`.

This file isolates the K⁺-side primary definition with basic API.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* Vandiver 1929, *Fermat's Last Theorem and the Second Factor in the
  Cyclotomic Class Number*.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

section PrimaryPlus

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

section CyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- `(ζ-1) ∣ cyclotomicUnit_k + cyclotomicUnit_{p-k}` for `k ≤ p`. Proof:
each `cyclotomicUnit_k - k` and `cyclotomicUnit_{p-k} - (p-k)` is
divisible by `(ζ-1)`; summing gives `(ζ-1) ∣ (cycl_k + cycl_{p-k} - p)`.
Since `(ζ-1) ∣ p` in `𝓞 K`, the sum itself is divisible. -/
theorem zetaSubOne_dvd_cyclotomicUnit_add_cyclotomicUnit_p_sub
    {k : ℕ} (hk : k ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (cyclotomicUnit p K k + cyclotomicUnit p K (p - k)) := by
  have h1 := zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k
  have h2 := zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K (p - k)
  have h_sum := dvd_add h1 h2
  have h_simplify :
      cyclotomicUnit p K k - (k : 𝓞 K) +
        (cyclotomicUnit p K (p - k) - ((p - k : ℕ) : 𝓞 K)) =
      cyclotomicUnit p K k + cyclotomicUnit p K (p - k) -
        ((k : 𝓞 K) + ((p - k : ℕ) : 𝓞 K)) := by ring
  rw [h_simplify] at h_sum
  have h_eq : (k : 𝓞 K) + ((p - k : ℕ) : 𝓞 K) = (p : 𝓞 K) := by
    have hsum : (k : ℕ) + (p - k) = p := Nat.add_sub_cancel' hk
    have : ((k + (p - k) : ℕ) : 𝓞 K) = (p : 𝓞 K) := by
      rw [hsum]
    push_cast at this
    exact this
  rw [h_eq] at h_sum
  -- (ζ - 1) ∣ p in 𝓞 K. Use zeta_sub_one_dvd_Int_iff from flt-regular.
  have h_p : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ ((p : ℤ) : 𝓞 K) :=
    (zeta_sub_one_dvd_Int_iff (zeta_spec p ℚ K)).mpr (dvd_refl _)
  have hp_int : ((p : ℤ) : 𝓞 K) = (p : 𝓞 K) := by push_cast; rfl
  rw [hp_int] at h_p
  have := dvd_add h_sum h_p
  have h_cancel :
      cyclotomicUnit p K k + cyclotomicUnit p K (p - k) - (p : 𝓞 K) +
        (p : 𝓞 K) =
      cyclotomicUnit p K k + cyclotomicUnit p K (p - k) := by ring
  rwa [h_cancel] at this

/-- **`(ζ-1)^2 ∣ ζ^k + ζ^{p-k} - 2`** for `k ≤ p`. Combines
`(ζ-1) ∣ (cyclotomicUnit_k + cyclotomicUnit_{p-k})` with the
factoring `ζ^k - 1 = (ζ-1) · cyclotomicUnit_k` etc. -/
theorem zetaSubOne_sq_dvd_zeta_pow_add_zeta_pow_sub_two
    {k : ℕ} (hk : k ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) - 2) := by
  -- ζ^k + ζ^{p-k} - 2 = (ζ^k - 1) + (ζ^{p-k} - 1)
  --                  = (ζ - 1)·cyclotomicUnit_k + (ζ - 1)·cyclotomicUnit_{p-k}
  --                  = (ζ - 1)·(cyclotomicUnit_k + cyclotomicUnit_{p-k})
  -- and (ζ - 1) ∣ (cyclotomicUnit_k + cyclotomicUnit_{p-k}).
  have htel_k : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K k =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1 := by
    have h := one_sub_zeta_mul_cyclotomicUnit p K k
    linear_combination -h
  have htel_pk : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K (p - k) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) - 1 := by
    have h := one_sub_zeta_mul_cyclotomicUnit p K (p - k)
    linear_combination -h
  have h_factor : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) - 2 =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) *
        (cyclotomicUnit p K k + cyclotomicUnit p K (p - k)) := by
    linear_combination -htel_k - htel_pk
  rw [h_factor, sq]
  exact mul_dvd_mul_left _
    (zetaSubOne_dvd_cyclotomicUnit_add_cyclotomicUnit_p_sub p K hk)

/-- **Equivalent form via `zetaSubOne`.** -/
theorem zetaSubOne_pow_two_dvd_factor_sub_taylor (a b : ℤ) (k : ℕ) :
    (zetaSubOne p K) ^ 2 ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        (((a + b : ℤ) : 𝓞 K) +
          (b : 𝓞 K) * (k : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) :=
  zetaSubOne_sq_dvd_factor_sub_taylor p K a b k

/-- **Second-order refinement of `cyclotomicUnit_k - k`.**
`cyclotomicUnit k - k - (k.choose 2)·(ζ - 1)` is divisible by `(ζ - 1)²`.
This is the next-order Taylor coefficient of `cyclotomicUnit k` viewed as a
power series in `(ζ - 1)`. Proved by induction on `k` using Pascal's rule
`(k+1).choose 2 = k.choose 2 + k` and the order-2 Taylor of `ζ^k`. -/
theorem zetaSubOne_sq_dvd_cyclotomicUnit_sub_natCast_sub_choose_mul (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      (cyclotomicUnit p K k - (k : 𝓞 K) -
        (k.choose 2 : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) := by
  induction k with
  | zero =>
    simp [cyclotomicUnit_zero]
  | succ n ih =>
    rw [cyclotomicUnit_succ]
    have h_taylor := zetaSubOne_sq_dvd_zeta_pow_sub_one_sub_natCast_mul p K n
    -- Pascal: (n+1).choose 2 = n + n.choose 2.
    have h_pascal : (((n + 1).choose 2 : ℕ) : 𝓞 K) =
        (n.choose 2 : 𝓞 K) + (n : 𝓞 K) := by
      have : (n + 1).choose 2 = n + n.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast [this]
      ring
    -- Combine IH (z² ∣ cyc n - n - n.choose 2 · z) with order-2 Taylor (z² ∣ ζ^n - 1 - n·z).
    have h_sum := dvd_add ih h_taylor
    have h_id : (cyclotomicUnit p K n - (n : 𝓞 K) -
                  (n.choose 2 : 𝓞 K) *
                  (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) +
                ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ n - 1) -
                  (n : 𝓞 K) *
                  (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) =
                (cyclotomicUnit p K n +
                  ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ n -
                  ((n + 1 : ℕ) : 𝓞 K) -
                  (((n + 1).choose 2 : ℕ) : 𝓞 K) *
                    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) := by
      rw [h_pascal]
      push_cast
      ring
    rw [← h_id]
    exact h_sum

/-- **Order-3 Taylor expansion modulo `(ζ - 1)^3`.** For integers `a, b`
and any natural `k`, the cyclotomic factor `a + ζ^k · b` is congruent to
`(a + b) + b·k·(ζ - 1) + b·(k.choose 2)·(ζ - 1)²` modulo `(ζ - 1)^3`.

This is the next-order refinement of `zetaSubOne_sq_dvd_factor_sub_taylor`,
adding the quadratic-in-`(ζ - 1)` term. Used in the deep step of the
Mirimanoff polynomial vanishing argument. -/
theorem zetaSubOne_cube_dvd_factor_sub_taylor2 (a b : ℤ) (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        (((a + b : ℤ) : 𝓞 K) +
          (b : 𝓞 K) * (k : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) +
          (b : 𝓞 K) * (k.choose 2 : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2)) := by
  -- Strategy: ζ^k - 1 = (ζ-1)·cyclotomicUnit_k. Apply the second-order
  -- refinement: (ζ-1)² ∣ cyclotomicUnit_k - k - (k.choose 2)·(ζ-1).
  -- Multiplying by (ζ-1) gives:
  -- (ζ-1)³ ∣ (ζ-1)·(cyclotomicUnit_k - k - (k.choose 2)·(ζ-1))
  --        = (ζ-1)·cyclotomicUnit_k - k·(ζ-1) - (k.choose 2)·(ζ-1)²
  --        = (ζ^k - 1) - k·(ζ-1) - (k.choose 2)·(ζ-1)².
  -- Multiplying by b and adding a:
  -- (ζ-1)³ ∣ b·(ζ^k - 1) - bk·(ζ-1) - b·(k.choose 2)·(ζ-1)²
  --        = b·ζ^k - b - bk·(ζ-1) - b·(k.choose 2)·(ζ-1)².
  -- Adding a:
  -- (ζ-1)³ ∣ (a + b·ζ^k) - (a + b) - bk·(ζ-1) - b·(k.choose 2)·(ζ-1)².
  have htel : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K k =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1 := by
    have h := one_sub_zeta_mul_cyclotomicUnit p K k
    linear_combination -h
  obtain ⟨w, hw⟩ : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      cyclotomicUnit p K k - (k : 𝓞 K) -
        (k.choose 2 : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) :=
    zetaSubOne_sq_dvd_cyclotomicUnit_sub_natCast_sub_choose_mul p K k
  refine ⟨(b : 𝓞 K) * w, ?_⟩
  have hcast : ((a + b : ℤ) : 𝓞 K) = (a : 𝓞 K) + (b : 𝓞 K) := by push_cast; rfl
  rw [hcast]
  -- Direct algebraic manipulation:
  -- LHS = a + b·ζ^k - a - b - bk·(ζ-1) - b·(k.choose 2)·(ζ-1)²
  --     = b·(ζ^k - 1) - bk·(ζ-1) - b·(k.choose 2)·(ζ-1)²
  -- Using ζ^k - 1 = (ζ-1)·cyclotomicUnit_k:
  --     = b·(ζ-1)·cyclotomicUnit_k - bk·(ζ-1) - b·(k.choose 2)·(ζ-1)²
  --     = b·(ζ-1)·(cyclotomicUnit_k - k - (k.choose 2)·(ζ-1))
  --     = b·(ζ-1)·((ζ-1)²·w)  [using hw]
  --     = b·(ζ-1)³·w
  --     = (ζ-1)³ · (b·w)
  linear_combination -(b : 𝓞 K) * htel +
    (b : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * hw

/-- **Equivalent form via `zetaSubOne` for the order-3 Taylor expansion.** -/
theorem zetaSubOne_pow_three_dvd_factor_sub_taylor2 (a b : ℤ) (k : ℕ) :
    (zetaSubOne p K) ^ 3 ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        (((a + b : ℤ) : 𝓞 K) +
          (b : 𝓞 K) * (k : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) +
          (b : 𝓞 K) * (k.choose 2 : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2)) :=
  zetaSubOne_cube_dvd_factor_sub_taylor2 p K a b k

/-- **Order-3 Taylor expansion of `ζ^m`:**
`(ζ - 1)^3 ∣ ζ^m - 1 - m·(ζ - 1) - (m.choose 2)·(ζ - 1)^2` in `𝓞 K`.
The proof uses `ζ^m - 1 = (ζ - 1)·cyclotomicUnit_m` and the second-order
refinement `(ζ - 1)² ∣ cyclotomicUnit_m - m - (m.choose 2)·(ζ - 1)`. -/
theorem zetaSubOne_cube_dvd_zeta_pow_sub_one_sub_natCast_mul_sub_choose_mul (m : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m - 1) -
        (m : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) -
        (m.choose 2 : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2) := by
  have htel : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K m =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m - 1 := by
    have h := one_sub_zeta_mul_cyclotomicUnit p K m
    linear_combination -h
  obtain ⟨w, hw⟩ : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      cyclotomicUnit p K m - (m : 𝓞 K) -
        (m.choose 2 : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) :=
    zetaSubOne_sq_dvd_cyclotomicUnit_sub_natCast_sub_choose_mul p K m
  refine ⟨w, ?_⟩
  -- (ζ^m - 1) - m·(ζ-1) - (m.choose 2)·(ζ-1)²
  -- = (ζ-1)·cyclotomicUnit_m - m·(ζ-1) - (m.choose 2)·(ζ-1)²
  -- = (ζ-1)·(cyclotomicUnit_m - m - (m.choose 2)·(ζ-1))
  -- = (ζ-1)·(ζ-1)²·w = (ζ-1)³·w
  linear_combination -htel + (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * hw

/-- **`(ζ-1)^3 ∣ p` for `p ≥ 5`** in `𝓞 K`. Direct corollary of
`zetaSubOne_pow_p_sub_one_dvd_p`: `(ζ-1)³ ∣ (ζ-1)^{p-1} ∣ p` when
`p - 1 ≥ 3`, i.e., `p ≥ 4`, so `p ≥ 5` for primes. -/
theorem zetaSubOne_cube_dvd_p (hp_five : 5 ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣ ((p : ℕ) : 𝓞 K) :=
  (pow_dvd_pow _ (by omega : 3 ≤ p - 1)).trans
    (zetaSubOne_pow_p_sub_one_dvd_p (p := p) (K := K))

/-- **`γ^p` is congruent to an integer modulo `(ζ-1)^3`** for `p ≥ 5`.
`exists_int_sub_pow_prime_dvd` gives `m ∈ ℤ` with `γ^p ≡ m (mod p)`,
and `(ζ-1)^3 ∣ p` lifts the congruence to `(ζ-1)^3`. -/
theorem exists_int_zetaSubOne_cube_dvd_pow_sub
    (hp_five : 5 ≤ p) (γ : 𝓞 K) :
    ∃ m : ℤ, (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣ (γ ^ p - (m : 𝓞 K)) := by
  obtain ⟨m, hm⟩ := exists_int_sub_pow_prime_dvd p γ
  refine ⟨m, ?_⟩
  rw [Ideal.mem_span_singleton] at hm
  have h_p_dvd : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣ ((p : ℕ) : 𝓞 K) :=
    zetaSubOne_cube_dvd_p (p := p) (K := K) hp_five
  have hp_cast : ((p : ℕ) : 𝓞 K) = (p : 𝓞 K) := by rfl
  rw [hp_cast] at h_p_dvd
  exact h_p_dvd.trans hm

/-- **Order-3 Taylor expansion of `v · γ^p` for real `v` and `p ≥ 5`.**

For real `v ∈ 𝓞 K` (with `σ(v) = v`) and any `γ ∈ 𝓞 K`, with `p ≥ 5`,
there exist integers `V₀, M` and an element `w ∈ 𝓞 K` such that
`v · γ^p ≡ V₀ · M + (ζ-1)² · w (mod (ζ-1)³)`.

This packages the order-3 Taylor expansion of the unit-times-power-power
component of the FLT case I decomposition. The (ζ-1)¹ coefficient vanishes
(by reality of v) and γ^p contributes only its constant term M ∈ ℤ
(by `exists_int_zetaSubOne_cube_dvd_pow_sub`). -/
theorem exists_int_zetaSubOne_cube_dvd_real_mul_pow_sub
    [IsCMField K] (hp_five : 5 ≤ p)
    {v : 𝓞 K} (hv_real : ringOfIntegersComplexConj K v = v) (γ : 𝓞 K) :
    ∃ (V₀ M : ℤ) (w : 𝓞 K),
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 3 ∣
        (v * γ ^ p - (V₀ : 𝓞 K) * (M : 𝓞 K) -
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 * w) := by
  have hp_odd : p ≠ 2 := by omega
  obtain ⟨V₀, hV₀⟩ := exists_int_zetaSubOne_sq_dvd_sub_of_real (p := p) (K := K) hp_odd hv_real
  obtain ⟨M, hM⟩ := exists_int_zetaSubOne_cube_dvd_pow_sub (p := p) (K := K) hp_five γ
  obtain ⟨w', hw'⟩ := hV₀
  refine ⟨V₀, M, w' * (M : 𝓞 K), ?_⟩
  have h_v_eq : v = (V₀ : 𝓞 K) + (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 * w' := by
    linear_combination hw'
  have h_id : v * γ ^ p - (V₀ : 𝓞 K) * (M : 𝓞 K) -
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 * (w' * (M : 𝓞 K)) =
      v * (γ ^ p - (M : 𝓞 K)) := by
    rw [h_v_eq]; ring
  rw [h_id]
  exact hM.mul_left v

/-- `(ζ - 1) ∣ (a + ζ^k · b)` if and only if `(ζ - 1) ∣ (a + b)`. -/
theorem zetaSubOne_dvd_factor_iff (a b : ℤ) (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
        ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ↔
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ ((a + b : ℤ) : 𝓞 K) := by
  have h := zetaSubOne_dvd_factor_sub_sum p K a b k
  -- h : (ζ-1) ∣ (a + ζ^k b - (a+b))
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · -- (ζ-1) ∣ (a + ζ^k b) and (ζ-1) ∣ (a + ζ^k b - (a+b)) ⇒ (ζ-1) ∣ (a+b)
    have := dvd_sub hd h
    have heq : ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K))
        - (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
          ((a + b : ℤ) : 𝓞 K)) = ((a + b : ℤ) : 𝓞 K) := by ring
    rwa [heq] at this
  · -- reverse direction
    have := dvd_add hd h
    have heq : ((a + b : ℤ) : 𝓞 K) +
        (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
          ((a + b : ℤ) : 𝓞 K)) =
        ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) := by ring
    rwa [heq] at this

/-- `(ζ - 1)` divides an integer `n` (cast to `𝓞 K`) if and only if
`p ∣ n`. Wrapper for flt-regular's `zeta_sub_one_dvd_Int_iff`. -/
theorem zetaSubOne_dvd_intCast_iff (n : ℤ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ ((n : ℤ) : 𝓞 K) ↔ (p : ℤ) ∣ n :=
  zeta_sub_one_dvd_Int_iff (zeta_spec p ℚ K)

/-- For integers `a, b, k`, `(ζ - 1) ∣ (a + ζ^k · b) ↔ p ∣ (a + b)`. -/
theorem zetaSubOne_dvd_factor_iff_p_dvd (a b : ℤ) (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
        ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ↔
      (p : ℤ) ∣ (a + b) := by
  rw [zetaSubOne_dvd_factor_iff, zetaSubOne_dvd_intCast_iff]

/-- The K-level multiplicative identity `(ζ - 1) · cyclotomicUnit = ζ^k - 1`
in K, lifted from the 𝓞 K version. -/
theorem zeta_sub_one_mul_cyclotomicUnit_in_K (k : ℕ) :
    (IsCyclotomicExtension.zeta p ℚ K - 1) *
        algebraMap (𝓞 K) K (cyclotomicUnit p K k) =
      IsCyclotomicExtension.zeta p ℚ K ^ k - 1 := by
  have h := zeta_sub_one_mul_cyclotomicUnit p K k
  have := congrArg (algebraMap (𝓞 K) K) h
  rw [map_mul, map_sub, map_sub, map_pow, map_one] at this
  exact this

/-- **Norm of the cyclotomic unit.** For `k` coprime to `p` (odd prime),
`Algebra.norm ℚ (cyclotomicUnit p K k) = 1`. -/
theorem cyclotomicUnit_norm_rat (k : ℕ) (hk : k.Coprime p) (hp_odd : p ≠ 2) :
    Algebra.norm ℚ (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) = (1 : ℚ) := by
  have h_K := zeta_sub_one_mul_cyclotomicUnit_in_K p K k
  have hp_pos : 0 < (p : ℚ) := by exact_mod_cast hp.1.pos
  have h_norm := congrArg (Algebra.norm ℚ : K → ℚ) h_K
  rw [map_mul, FLT37.zeta_pow_sub_one_norm_rat p K hp_odd k hk] at h_norm
  -- LHS: norm(ζ - 1) · norm(cyclotomicUnit) = p · norm(cyclotomicUnit)
  have h_zeta := FLT37.zetaSubOne_norm_rat p K hp_odd
  rw [FLT37.algebraMap_zetaSubOne] at h_zeta
  rw [h_zeta] at h_norm
  -- h_norm : p * norm(...) = p
  exact mul_left_cancel₀ hp_pos.ne' (h_norm.trans (mul_one _).symm)

/-- **Integer norm of the cyclotomic unit.** For `k` coprime to `p` (odd
prime), `Algebra.norm ℤ (cyclotomicUnit p K k) = 1`. -/
theorem cyclotomicUnit_norm_int (k : ℕ) (hk : k.Coprime p) (hp_odd : p ≠ 2) :
    Algebra.norm ℤ (cyclotomicUnit p K k) = (1 : ℤ) := by
  have h_rat := cyclotomicUnit_norm_rat p K k hk hp_odd
  have h_coe : ((Algebra.norm ℤ (cyclotomicUnit p K k) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) :=
    Algebra.coe_norm_int _
  rw [h_rat] at h_coe
  exact_mod_cast h_coe

/-- `cyclotomicUnit p K p = 0`, since `∑_{j=0}^{p-1} ζ^j = 0`
(cyclotomic identity). -/
theorem cyclotomicUnit_p_eq_zero : cyclotomicUnit p K p = 0 :=
  (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.geom_sum_eq_zero
    (Nat.lt_of_lt_of_le one_lt_two hp.1.two_le)

/-- `cyclotomicUnit p K (a + p) = cyclotomicUnit p K a`: the cyclotomic
unit is periodic in its index modulo `p`. -/
theorem cyclotomicUnit_add_p (a : ℕ) :
    cyclotomicUnit p K (a + p) = cyclotomicUnit p K a := by
  rw [cyclotomicUnit_add, cyclotomicUnit_p_eq_zero, mul_zero, add_zero]

/-- `cyclotomicUnit p K (p + 1) = 1`. -/
theorem cyclotomicUnit_p_add_one : cyclotomicUnit p K (p + 1) = 1 := by
  rw [add_comm, cyclotomicUnit_add_p, cyclotomicUnit_one]

/-- Iterated periodicity: `cyclotomicUnit (a + m·p) = cyclotomicUnit a`. -/
theorem cyclotomicUnit_add_mul_p (a m : ℕ) :
    cyclotomicUnit p K (a + m * p) = cyclotomicUnit p K a := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, cyclotomicUnit_add_p, ih]

/-- `cyclotomicUnit p K k` only depends on `k mod p`. -/
theorem cyclotomicUnit_mod_p (k : ℕ) :
    cyclotomicUnit p K k = cyclotomicUnit p K (k % p) := by
  conv_lhs => rw [← Nat.mod_add_div k p, mul_comm p (k / p)]
  exact cyclotomicUnit_add_mul_p p K (k % p) (k / p)

/-- `cyclotomicUnit p K (k₁ + k₂) = cyclotomicUnit p K (k₁ + k₂ mod p)`,
combining the mod_p form with the additive structure. -/
theorem cyclotomicUnit_add_mod_p (k₁ k₂ : ℕ) :
    cyclotomicUnit p K (k₁ + k₂) = cyclotomicUnit p K ((k₁ + k₂) % p) :=
  cyclotomicUnit_mod_p p K (k₁ + k₂)

/-- `cyclotomicUnit p K k = 0 ↔ p ∣ k`. -/
theorem cyclotomicUnit_eq_zero_iff (k : ℕ) :
    cyclotomicUnit p K k = 0 ↔ p ∣ k := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => ?_⟩
  · rw [cyclotomicUnit_mod_p p K k] at h
    rw [Nat.dvd_iff_mod_eq_zero]
    by_contra hne
    have hkmod_pos : 1 ≤ k % p := Nat.one_le_iff_ne_zero.mpr hne
    have hkmod_lt : k % p < p := Nat.mod_lt _ hp.1.pos
    have h_coprime : (k % p).Coprime p :=
      (Nat.coprime_of_lt_prime (Nat.one_le_iff_ne_zero.mp hkmod_pos)
        hkmod_lt hp.1).symm
    have h_unit : IsUnit (cyclotomicUnit p K (k % p)) :=
      isUnit_cyclotomicUnit p K (k % p) h_coprime hp.1.two_le
    rw [h] at h_unit
    exact (not_isUnit_zero) h_unit
  · rw [hm, mul_comm, ← Nat.zero_add (m * p), cyclotomicUnit_add_mul_p]
    exact cyclotomicUnit_zero p K

/-- `IsUnit (cyclotomicUnit p K k) ↔ ¬ p ∣ k`. -/
theorem isUnit_cyclotomicUnit_iff (k : ℕ) :
    IsUnit (cyclotomicUnit p K k) ↔ ¬ p ∣ k := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro hdvd
    rw [(cyclotomicUnit_eq_zero_iff p K k).mpr hdvd] at h
    exact not_isUnit_zero h
  · rw [Nat.dvd_iff_mod_eq_zero] at h
    have hkmod_pos : 1 ≤ k % p := Nat.one_le_iff_ne_zero.mpr h
    have hkmod_lt : k % p < p := Nat.mod_lt _ hp.1.pos
    have h_coprime : (k % p).Coprime p :=
      (Nat.coprime_of_lt_prime (Nat.one_le_iff_ne_zero.mp hkmod_pos)
        hkmod_lt hp.1).symm
    rw [cyclotomicUnit_mod_p p K k]
    exact isUnit_cyclotomicUnit p K (k % p) h_coprime hp.1.two_le

/-- `cyclotomicUnit` indexed by `k : ZMod p`, taking `k.val` as the
underlying natural number. Well-defined by `cyclotomicUnit_mod_p`. -/
noncomputable def cyclotomicUnitZMod (k : ZMod p) : 𝓞 K :=
  cyclotomicUnit p K k.val

theorem cyclotomicUnitZMod_natCast (k : ℕ) [NeZero p] :
    cyclotomicUnitZMod p K (k : ZMod p) = cyclotomicUnit p K k := by
  unfold cyclotomicUnitZMod
  rw [ZMod.val_natCast, ← cyclotomicUnit_mod_p]

/-- `cyclotomicUnitZMod p K 0 = 0`. -/
theorem cyclotomicUnitZMod_zero [NeZero p] :
    cyclotomicUnitZMod p K (0 : ZMod p) = 0 := by
  unfold cyclotomicUnitZMod
  rw [ZMod.val_zero, cyclotomicUnit_zero]

/-- `cyclotomicUnitZMod p K 1 = 1` for `p ≥ 2`. -/
theorem cyclotomicUnitZMod_one :
    cyclotomicUnitZMod p K (1 : ZMod p) = 1 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold cyclotomicUnitZMod
  rw [ZMod.val_one, cyclotomicUnit_one]

/-- `cyclotomicUnitZMod p K k = 0 ↔ k = 0`. -/
theorem cyclotomicUnitZMod_eq_zero_iff (k : ZMod p) :
    cyclotomicUnitZMod p K k = 0 ↔ k = 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold cyclotomicUnitZMod
  rw [cyclotomicUnit_eq_zero_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show (0 : ZMod p) = ((0 : ℕ) : ZMod p) from by push_cast; rfl,
      ← ZMod.natCast_zmod_val k, ZMod.natCast_eq_natCast_iff]
    exact (Nat.modEq_zero_iff_dvd).mpr h
  · subst h
    simp

/-- `IsUnit (cyclotomicUnitZMod p K k) ↔ k ≠ 0`. -/
theorem isUnit_cyclotomicUnitZMod_iff (k : ZMod p) :
    IsUnit (cyclotomicUnitZMod p K k) ↔ k ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold cyclotomicUnitZMod
  rw [isUnit_cyclotomicUnit_iff]
  refine ⟨fun h hk => ?_, fun h hdvd => ?_⟩
  · subst hk
    apply h
    simp
  · apply h
    rw [show (0 : ZMod p) = ((0 : ℕ) : ZMod p) from by push_cast; rfl,
      ← ZMod.natCast_zmod_val k, ZMod.natCast_eq_natCast_iff]
    exact (Nat.modEq_zero_iff_dvd).mpr hdvd

/-- For `k : (ZMod p)ˣ`, `cyclotomicUnitZMod p K (k : ZMod p)` is a unit. -/
theorem isUnit_cyclotomicUnitZMod_of_units (k : (ZMod p)ˣ) :
    IsUnit (cyclotomicUnitZMod p K (k : ZMod p)) :=
  (isUnit_cyclotomicUnitZMod_iff p K k.1).mpr k.ne_zero

/-- `cyclotomicUnit p K (p - 1) = -ζ^{p-1}`. From the cyclotomic
identity `∑_{j=0}^{p-1} ζ^j = 0`, we have
`∑_{j=0}^{p-2} ζ^j = -ζ^{p-1}`. -/
theorem cyclotomicUnit_p_sub_one :
    cyclotomicUnit p K (p - 1) = -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
  have hp_pos : 1 ≤ p := hp.1.pos
  have hp_eq : (p - 1) + 1 = p := Nat.sub_add_cancel hp_pos
  have key : cyclotomicUnit p K (p - 1) +
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) = 0 := by
    have hrec := cyclotomicUnit_succ p K (p - 1)
    rw [hp_eq] at hrec
    rw [← hrec, cyclotomicUnit_p_eq_zero]
  linear_combination key

/-- `cyclotomicUnit p K (p - 2) = -ζ^{p-2} - ζ^{p-1}` (for `p ≥ 2`).
Stepping back from `cyclotomicUnit_p_sub_one` via `cyclotomicUnit_succ`. -/
theorem cyclotomicUnit_p_sub_two (hp_three : 3 ≤ p) :
    cyclotomicUnit p K (p - 2) =
      -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 2) -
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
  have hp_eq : (p - 2) + 1 = p - 1 := by omega
  have hrec := cyclotomicUnit_succ p K (p - 2)
  rw [hp_eq] at hrec
  -- hrec: c_{p-1} = c_{p-2} + ζ^{p-2}
  -- so c_{p-2} = c_{p-1} - ζ^{p-2} = -ζ^{p-1} - ζ^{p-2}
  rw [cyclotomicUnit_p_sub_one] at hrec
  linear_combination -hrec

end CyclotomicUnits

/-! ## Real cyclotomic units `(1 - ζ^k)(1 - ζ^{-k})/((1 - ζ)(1 - ζ^{-1}))`

These are `σ`-fixed in `𝓞 K` and hence descend to elements of `𝓞 K⁺`.
They are the building blocks for Pollaczek's primary unit decomposition. -/

section RealCyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The real cyclotomic combination
`(cyclotomicUnit k) · σ(cyclotomicUnit k)` in `𝓞 K`. This is
automatically `σ`-fixed and corresponds to the K⁺-side cyclotomic
unit `(1 - ζ^k)(1 - ζ^{-k})/((1 - ζ)(1 - ζ^{-1}))`. -/
noncomputable def realCyclotomicUnit [IsCMField K] (k : ℕ) : 𝓞 K :=
  cyclotomicUnit p K k * ringOfIntegersComplexConj K (cyclotomicUnit p K k)

/-- `(ζ - 1) ∣ realCyclotomicUnit p K k - k^2` in `𝓞 K`. The proof
combines `cyclotomicUnit_k ≡ k (mod (ζ-1))` and
`σ(cyclotomicUnit_k) ≡ k (mod (ζ-1))` (the latter via
`zetaSubOne_dvd_complexConj_cyclotomicUnit_sub_natCast`). -/
theorem zetaSubOne_dvd_realCyclotomicUnit_sub_natCast_sq [IsCMField K]
    (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (realCyclotomicUnit p K k - ((k : 𝓞 K)) ^ 2) := by
  unfold realCyclotomicUnit
  -- realCyclotomicUnit_k = cyclotomicUnit_k · σ(cyclotomicUnit_k).
  -- mod (ζ-1): both factors ≡ k, so product ≡ k^2.
  have h1 := zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k
  have h2 := zetaSubOne_dvd_complexConj_cyclotomicUnit_sub_natCast p K k
  -- (cyclotomicUnit_k - k) and (σ(cyclotomicUnit_k) - k) divisible by (ζ-1).
  -- Product trick: A·B - k^2 = (A - k)·B + k·(B - k)
  obtain ⟨w₁, hw₁⟩ := h1
  obtain ⟨w₂, hw₂⟩ := h2
  refine ⟨ringOfIntegersComplexConj K (cyclotomicUnit p K k) * w₁ + (k : 𝓞 K) * w₂, ?_⟩
  -- Goal: cyclotomicUnit_k · σ(cyclotomicUnit_k) - k^2 = (ζ-1) · (...)
  -- A·B - k^2 = (A-k)·B + k·(B-k); use hw₁ : A - k = (ζ-1)w₁ and hw₂ : B - k = (ζ-1)w₂.
  linear_combination ringOfIntegersComplexConj K (cyclotomicUnit p K k) * hw₁ +
    (k : 𝓞 K) * hw₂

/-- For `k = 1`, the real cyclotomic combination is `1`. -/
theorem realCyclotomicUnit_one [IsCMField K] :
    realCyclotomicUnit p K 1 = 1 := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_one, map_one, mul_one]

/-- For `k = 0`, the real cyclotomic combination is `0`. -/
theorem realCyclotomicUnit_zero [IsCMField K] :
    realCyclotomicUnit p K 0 = 0 := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_zero, zero_mul]

/-- For `k = 2`, the real cyclotomic combination is
`(1 + ζ) · (1 + ζ^(p-1))`. -/
theorem realCyclotomicUnit_two [IsCMField K] :
    realCyclotomicUnit p K 2 =
      (1 + ((zeta_spec p ℚ K).toInteger : 𝓞 K)) *
        (1 + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_two, map_add, map_one]
  have hconj_zeta : ringOfIntegersComplexConj K
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) :=
    complexConj_apply_zeta (p := p) (K := K)
  rw [hconj_zeta]

/-- For `k = 3`, the real cyclotomic combination is
`(1 + ζ + ζ²) · (1 + ζ^{p-1} + ζ^{2(p-1)})`. -/
theorem realCyclotomicUnit_three [IsCMField K] :
    realCyclotomicUnit p K 3 =
      (1 + ((zeta_spec p ℚ K).toInteger : 𝓞 K) +
         ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ 2) *
        (1 + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) +
         ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * (p - 1))) := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_three, map_add, map_add, map_one, map_pow]
  have hconj_zeta : ringOfIntegersComplexConj K
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) :=
    complexConj_apply_zeta (p := p) (K := K)
  rw [hconj_zeta, ← pow_mul]
  ring

/-- For `k = p`, the real cyclotomic combination is `0`. -/
theorem realCyclotomicUnit_p_eq_zero [IsCMField K] :
    realCyclotomicUnit p K p = 0 := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_p_eq_zero, zero_mul]

/-- The real cyclotomic combination is periodic in its index modulo `p`. -/
theorem realCyclotomicUnit_add_p [IsCMField K] (a : ℕ) :
    realCyclotomicUnit p K (a + p) = realCyclotomicUnit p K a := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_add_p]

/-- `realCyclotomicUnit p K (p + 1) = 1`. -/
theorem realCyclotomicUnit_p_add_one [IsCMField K] :
    realCyclotomicUnit p K (p + 1) = 1 := by
  rw [add_comm, realCyclotomicUnit_add_p, realCyclotomicUnit_one]

/-- Iterated periodicity for the real cyclotomic combination. -/
theorem realCyclotomicUnit_add_mul_p [IsCMField K] (a m : ℕ) :
    realCyclotomicUnit p K (a + m * p) = realCyclotomicUnit p K a := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_add_mul_p]

/-- `realCyclotomicUnit p K k` only depends on `k mod p`. -/
theorem realCyclotomicUnit_mod_p [IsCMField K] (k : ℕ) :
    realCyclotomicUnit p K k = realCyclotomicUnit p K (k % p) := by
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_mod_p]

/-- `realCyclotomicUnit p K k = 0 ↔ p ∣ k`. -/
theorem realCyclotomicUnit_eq_zero_iff [IsCMField K] (k : ℕ) :
    realCyclotomicUnit p K k = 0 ↔ p ∣ k := by
  unfold realCyclotomicUnit
  rw [mul_eq_zero, cyclotomicUnit_eq_zero_iff]
  refine ⟨?_, fun h => Or.inl h⟩
  rintro (h | h)
  · exact h
  · -- σ(cyclotomicUnit k) = 0 implies cyclotomicUnit k = 0 (σ is injective)
    have := (ringOfIntegersComplexConj K).injective
      (h.trans (map_zero (ringOfIntegersComplexConj K)).symm)
    exact (cyclotomicUnit_eq_zero_iff p K k).mp this

/-- For `k = p - 1`, the real cyclotomic combination is `1`.
Using `cyclotomicUnit (p-1) = -ζ^(p-1)` and `σ(ζ) = ζ^(p-1)`,
the combination simplifies to `ζ^p = 1`. -/
theorem realCyclotomicUnit_p_sub_one [IsCMField K] :
    realCyclotomicUnit p K (p - 1) = 1 := by
  have hp_pos : 1 ≤ p := hp.1.pos
  unfold realCyclotomicUnit
  rw [cyclotomicUnit_p_sub_one, map_neg, map_pow]
  have hconj_zeta_eq : ringOfIntegersComplexConj K
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
    apply RingOfIntegers.ext
    push_cast
    have hzeta_eq : ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
        (zeta_spec p ℚ K).toInteger := rfl
    rw [hzeta_eq]
    exact_mod_cast complexConj_apply_zeta (p := p) (K := K)
  rw [hconj_zeta_eq, ← pow_mul]
  have hζp : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  have hkey : (-((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) *
      -(((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((p - 1) * (p - 1))) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((p - 1) + (p - 1) * (p - 1)) := by
    rw [neg_mul_neg, ← pow_add]
  rw [hkey]
  have hexp : (p - 1) + (p - 1) * (p - 1) = (p - 1) * p := by
    have : (p - 1) * p = (p - 1) * ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp_pos]
    rw [this, Nat.mul_add, Nat.mul_one, Nat.add_comm]
  rw [hexp, mul_comm (p - 1) p, pow_mul, hζp, one_pow]

/-- The real cyclotomic combination is fixed by complex conjugation. -/
theorem realCyclotomicUnit_complexConj [IsCMField K] (k : ℕ) :
    ringOfIntegersComplexConj K (realCyclotomicUnit p K k) =
      realCyclotomicUnit p K k := by
  unfold realCyclotomicUnit
  rw [map_mul]
  rw [show ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      cyclotomicUnit p K k from by
    apply RingOfIntegers.ext
    simp]
  ring



/-- **Integer norm of the real cyclotomic combination.** For `k` coprime
to `p` (odd prime), `Algebra.norm ℤ (realCyclotomicUnit p K k) = 1`. -/
theorem realCyclotomicUnit_norm_int [IsCMField K] (k : ℕ) (hk : k.Coprime p)
    (hp_odd : p ≠ 2) :
    Algebra.norm ℤ (realCyclotomicUnit p K k) = (1 : ℤ) := by
  -- realCyclotomicUnit = cyclotomicUnit · σ(cyclotomicUnit)
  -- norm(σ x) = norm(x), so norm(realCyclotomicUnit) = norm(cyclotomicUnit)^2 = 1
  unfold realCyclotomicUnit
  rw [map_mul]
  have h_conj : Algebra.norm ℤ (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      Algebra.norm ℤ (cyclotomicUnit p K k) := by
    apply (algebraMap ℤ ℚ).injective_int
    have h1 := Algebra.coe_norm_int (ringOfIntegersComplexConj K (cyclotomicUnit p K k))
    have h2 := Algebra.coe_norm_int (cyclotomicUnit p K k)
    -- transit through ℚ-norm
    have h_q : Algebra.norm ℚ (algebraMap (𝓞 K) K
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k))) =
        Algebra.norm ℚ (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) := by
      have h_eq : algebraMap (𝓞 K) K
          (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
          BernoulliRegular.complexConjRat (p := p) (K := K) hp_odd
            (algebraMap (𝓞 K) K (cyclotomicUnit p K k)) := by
        change ((ringOfIntegersComplexConj K (cyclotomicUnit p K k) : 𝓞 K) : K) =
          BernoulliRegular.complexConjRat (p := p) (K := K) hp_odd
            ((cyclotomicUnit p K k : 𝓞 K) : K)
        rw [coe_ringOfIntegersComplexConj]
        rfl
      rw [h_eq]
      exact Algebra.norm_eq_of_algEquiv
        (BernoulliRegular.complexConjRat (p := p) (K := K) hp_odd) _
    change ((algebraMap ℤ ℚ) (Algebra.norm ℤ _) : ℚ) =
      ((algebraMap ℤ ℚ) (Algebra.norm ℤ _))
    rw [show (algebraMap ℤ ℚ) (Algebra.norm ℤ
      (ringOfIntegersComplexConj K (cyclotomicUnit p K k))) =
      ((Algebra.norm ℤ (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) : ℤ) : ℚ) from rfl,
      show (algebraMap ℤ ℚ) (Algebra.norm ℤ (cyclotomicUnit p K k)) =
        ((Algebra.norm ℤ (cyclotomicUnit p K k) : ℤ) : ℚ) from rfl, h1, h2]
    exact h_q
  rw [h_conj, ← sq]
  rw [cyclotomicUnit_norm_int p K k hk hp_odd]
  ring

/-- The image of `cyclotomicUnit k` modulo `ζ - 1` is the rational integer `k`. -/
theorem zetaSubOne_dvd_cyclotomicUnit_succ_sub_succ_natCast (k : ℕ) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      cyclotomicUnit p K (k + 1) - ((k + 1 : ℕ) : 𝓞 K) :=
  zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K (k + 1)

/-- Boundary case: `cyclotomicUnit p K 1 - 1 = 0` is trivially divisible
by `ζ - 1`. -/
theorem zetaSubOne_dvd_cyclotomicUnit_one_sub_one :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      cyclotomicUnit p K 1 - (1 : 𝓞 K) := by
  rw [cyclotomicUnit_one, sub_self]
  exact dvd_zero _

/-- Existence of an explicit witness for the cyclotomicUnit ≡ k congruence. -/
theorem exists_cyclotomicUnit_sub_natCast_eq (k : ℕ) :
    ∃ α : 𝓞 K, cyclotomicUnit p K k - (k : 𝓞 K) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * α :=
  zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k

/-- `realCyclotomicUnit k ≡ k² (mod ζ - 1)` in `𝓞 K`. -/
theorem zetaSubOne_dvd_realCyclotomicUnit_sub_sq [IsCMField K] (k : ℕ) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 := by
  -- Combine cyclotomicUnit ≡ k and σ(cyclotomicUnit) ≡ k modulo ζ - 1
  have h_diff : realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 =
      cyclotomicUnit p K k *
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k) - (k : 𝓞 K)) +
      (k : 𝓞 K) * (cyclotomicUnit p K k - (k : 𝓞 K)) := by
    change cyclotomicUnit p K k * ringOfIntegersComplexConj K (cyclotomicUnit p K k)
        - (k : 𝓞 K) ^ 2 = _
    ring
  rw [h_diff]
  exact dvd_add
    ((zetaSubOne_dvd_complexConj_cyclotomicUnit_sub_natCast p K k).mul_left _)
    ((zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k).mul_left _)

/-- For `k = 2`, `realCyclotomicUnit p K 2 ≡ 4 (mod ζ - 1)`. -/
theorem zetaSubOne_dvd_realCyclotomicUnit_two_sub_four [IsCMField K] :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      realCyclotomicUnit p K 2 - (4 : 𝓞 K) := by
  have h := zetaSubOne_dvd_realCyclotomicUnit_sub_sq p K 2
  convert h using 1
  push_cast
  ring

/-- For `k = 3`, `realCyclotomicUnit p K 3 ≡ 9 (mod ζ - 1)`. -/
theorem zetaSubOne_dvd_realCyclotomicUnit_three_sub_nine [IsCMField K] :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      realCyclotomicUnit p K 3 - (9 : 𝓞 K) := by
  have h := zetaSubOne_dvd_realCyclotomicUnit_sub_sq p K 3
  convert h using 1
  push_cast
  ring

/-- For `k = p - 1`, `realCyclotomicUnit p K (p - 1) = 1` (proved separately
via the explicit ζ-formulas), congruent to `(p-1)² ≡ 1 (mod ζ - 1)`. -/
theorem zetaSubOne_dvd_realCyclotomicUnit_one_sub_one [IsCMField K] :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      realCyclotomicUnit p K 1 - (1 : 𝓞 K) := by
  rw [realCyclotomicUnit_one]
  simp

/-- Existence of an explicit witness for the realCyclotomicUnit ≡ k² congruence. -/
theorem exists_realCyclotomicUnit_sub_sq_eq [IsCMField K] (k : ℕ) :
    ∃ γ : 𝓞 K, realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * γ :=
  zetaSubOne_dvd_realCyclotomicUnit_sub_sq p K k

/-- The real cyclotomic combination is a unit when `k` is coprime to `p`. -/
theorem isUnit_realCyclotomicUnit [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnit p K k) := by
  unfold realCyclotomicUnit
  exact (isUnit_cyclotomicUnit p K k hk hp_two).mul
    ((isUnit_cyclotomicUnit p K k hk hp_two).map
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)

/-- The K-side real cyclotomic unit, packaged as `(𝓞 K)ˣ` when `k`
is coprime to `p`. -/
noncomputable def realCyclotomicUnitUnit [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) : (𝓞 K)ˣ :=
  (isUnit_realCyclotomicUnit p K k hk hp_two).unit

@[simp]
theorem realCyclotomicUnitUnit_val [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitUnit p K k hk hp_two : 𝓞 K) = realCyclotomicUnit p K k :=
  IsUnit.unit_spec _

end RealCyclotomicUnits
end PrimaryPlus
end FLT37

end BernoulliRegular

end

import HasseWeil.PowerSeriesHelpers
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# The Formal Group of an Elliptic Curve (Silverman Ch. IV)
-/

open WeierstrassCurve PowerSeries Finset

namespace HasseWeil

variable {R : Type*} [CommRing R]

def conv₂ (f : ℕ → R) (n : ℕ) : R :=
  (range (n + 1)).sum fun i ↦ f i * f (n - i)

def conv₃ (f : ℕ → R) (n : ℕ) : R :=
  (range (n + 1)).sum fun i ↦
    (range (n - i + 1)).sum fun j ↦ f i * f j * f (n - i - j)

/-! ### 1. w(z) and u(z) -/

def formalW_step (W : WeierstrassCurve R) (n : ℕ) (ih : ∀ m, m < n → R) : R :=
  if n < 3 then 0 else if n = 3 then 1 else
  let w : ℕ → R := fun m ↦ if h : m < n then ih m h else 0
  W.a₁ * w (n-1) + W.a₂ * w (n-2) + W.a₃ * conv₂ w n +
  W.a₄ * conv₂ w (n-1) + W.a₆ * conv₃ w n

noncomputable def formalW_coeff (W : WeierstrassCurve R) : ℕ → R :=
  WellFoundedRelation.wf.fix (formalW_step W)

noncomputable def formalW (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalW_coeff W)

noncomputable def formalU_coeff (W : WeierstrassCurve R) : ℕ → R :=
  fun n ↦ formalW_coeff W (n + 3)

noncomputable def formalPoly (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  let z : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0
  let w : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1
  z ^ 3 + MvPowerSeries.C W.a₁ * z * w + MvPowerSeries.C W.a₂ * z ^ 2 * w +
  MvPowerSeries.C W.a₃ * w ^ 2 + MvPowerSeries.C W.a₄ * z * w ^ 2 +
  MvPowerSeries.C W.a₆ * w ^ 3

/-! ### 2. The formal inverse i(z) = -z/(1 - a₁z - a₃z³u(z)) -/

noncomputable def invDenom_coeff (W : WeierstrassCurve R) : ℕ → R :=
  WellFoundedRelation.wf.fix fun n ih ↦
    if n = 0 then 1 else
    let d : ℕ → R := fun m ↦ if h : m < n then ih m h else 0
    W.a₁ * d (n - 1) +
      (if n ≥ 3 then W.a₃ * (range (n - 2)).sum fun k ↦
        formalU_coeff W k * d (n - 3 - k) else 0)

noncomputable def formalInverse_coeff (W : WeierstrassCurve R) : ℕ → R :=
  fun n ↦ if n = 0 then 0 else -(invDenom_coeff W (n - 1))

noncomputable def formalInverse (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalInverse_coeff W)

/-! ### 3. Bivariate helpers -/

def bmul (f g : ℕ → ℕ → R) (i j : ℕ) : R :=
  (range (i + 1)).sum fun a ↦ (range (j + 1)).sum fun b ↦
    f a b * g (i - a) (j - b)

-- Inverse of bivariate unit power series (f₀₀ = 1).
-- Well-founded on i + j; all recursive calls have strictly smaller total degree.
-- Bivariate unit inversion: g·f = 1 where f₀₀ = 1.
-- g_{ij} = [i=0∧j=0] - Σ_{(a,b)≠(i,j), a≤i, b≤j} g_{ab}·f_{i-a,j-b}
-- Well-founded on (i+j, i) with lexicographic order.
-- We use WellFounded.fix on ℕ (the total degree) to define all binv coefficients.
-- At total degree N, g_{ij} depends on g_{ab} with a+b < N (already computed).
-- This avoids 2D recursion issues.
noncomputable def binv_by_degree (f : ℕ → ℕ → R) : ℕ → (ℕ → ℕ → R) :=
  WellFoundedRelation.wf.fix fun N ih ↦
    -- ih N' hN' gives all g_{ab} with a + b = N' for N' < N
    let g_prev : ℕ → ℕ → R := fun a b ↦
      if h : a + b < N then (ih (a + b) h) a b else 0
    -- Now compute g_{ij} for i + j = N
    fun i j ↦
      if i + j ≠ N then 0  -- not this degree level
      else if i = 0 ∧ j = 0 then 1
      else -(range (i + 1)).sum fun a ↦ (range (j + 1)).sum fun b ↦
        if a = i ∧ b = j then 0
        else g_prev a b * f (i - a) (j - b)

noncomputable def binv_aux (f : ℕ → ℕ → R) (i j : ℕ) : R :=
  binv_by_degree f (i + j) i j

noncomputable def binv (f : ℕ → ℕ → R) (i j : ℕ) : R :=
  binv_aux f i j

def bpow (f : ℕ → ℕ → R) : ℕ → ℕ → ℕ → R
  | i, j, 0 => if i = 0 ∧ j = 0 then 1 else 0
  | i, j, (n + 1) => bmul f (bpow f · · n) i j

noncomputable def bcomp (h : ℕ → R) (s : ℕ → ℕ → R) (i j : ℕ) : R :=
  (range (i + j + 1)).sum fun n ↦ h n * bpow s i j n

/-! ### 4. The formal group law F(z₁,z₂) -/

structure FormalGroupLaw (R : Type*) [CommRing R] where
  toMvPowerSeries : MvPowerSeries (Fin 2) R

noncomputable def formalGroupLaw_coeff (W : WeierstrassCurve R) :
    (Fin 2 →₀ ℕ) → R :=
  fun d ↦ let i := d 0; let j := d 1
  if i = 0 then (if j = 1 then 1 else 0)
  else if j = 0 then (if i = 1 then 1 else 0)
  else if i + j = 2 then -W.a₁
  else if i + j = 3 then -W.a₂
  else if i + j = 4 then
    (if i = 2 ∧ j = 2 then W.a₁ * W.a₂ - 3 * W.a₃ else -(2 * W.a₃))
  else
    -- Degree ≥ 5: F = i(z₃) where z₃ = -B·A⁻¹ - z₁ - z₂
    let lam : ℕ → ℕ → R := fun a b ↦ formalW_coeff W (a + b + 1)
    let w1 : ℕ → ℕ → R := fun a b ↦ if b = 0 then formalW_coeff W a else 0
    let nu : ℕ → ℕ → R := fun a b ↦
      w1 a b - (if a ≥ 1 then lam (a - 1) b else 0)
    let A : ℕ → ℕ → R := fun a b ↦
      (if a = 0 ∧ b = 0 then 1 else 0) + W.a₂ * lam a b +
      W.a₄ * bmul lam lam a b + W.a₆ * bmul lam (bmul lam lam) a b
    let B : ℕ → ℕ → R := fun a b ↦
      W.a₁ * lam a b + W.a₂ * nu a b + W.a₃ * bmul lam lam a b +
      2 * W.a₄ * bmul lam nu a b + 3 * W.a₆ * bmul (bmul lam lam) nu a b
    let z3 : ℕ → ℕ → R := fun a b ↦
      -(bmul B (binv A) a b) -
      (if a = 1 ∧ b = 0 then 1 else 0) - (if a = 0 ∧ b = 1 then 1 else 0)
    bcomp (formalInverse_coeff W) z3 i j

noncomputable def formalGroupLaw (W : WeierstrassCurve R) : FormalGroupLaw R :=
  ⟨fun d ↦ formalGroupLaw_coeff W d⟩

/-! ### 5. The invariant differential ω(z)/dz = 1/F_X(0,z) -/

noncomputable def formalGroupLaw_dX_at_zero (W : WeierstrassCurve R) : ℕ → R :=
  fun n ↦ formalGroupLaw_coeff W (Finsupp.single 0 1 + Finsupp.single 1 n)

noncomputable def formalDiffCoeff (W : WeierstrassCurve R) : ℕ → R :=
  WellFoundedRelation.wf.fix fun n ih ↦
    if n = 0 then 1
    else -(range n).sum fun k ↦
      (if h : k < n then ih k h else 0) * formalGroupLaw_dX_at_zero W (n - k)

noncomputable def formalDiff (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalDiffCoeff W)

/-! ### Properties -/

variable (W : WeierstrassCurve R)

theorem formalW_coeff_three : formalW_coeff W 3 = 1 := by
  simp [formalW_coeff, WellFounded.fix_eq, formalW_step]

theorem formalW_coeff_zero : formalW_coeff W 0 = 0 := by
  simp [formalW_coeff, WellFounded.fix_eq, formalW_step]

theorem formalW_coeff_one : formalW_coeff W 1 = 0 := by
  simp [formalW_coeff, WellFounded.fix_eq, formalW_step]

theorem formalW_coeff_two : formalW_coeff W 2 = 0 := by
  simp [formalW_coeff, WellFounded.fix_eq, formalW_step]

theorem formalU_coeff_zero : formalU_coeff W 0 = 1 := formalW_coeff_three W

theorem formalDiffCoeff_zero : formalDiffCoeff W 0 = 1 := by
  simp [formalDiffCoeff, WellFounded.fix_eq]

/-! ### The defining recurrence for `formalW`

The series `formalW W` satisfies the Silverman IV.1.1 recurrence:
`w(z) = z³ + a₁zw + a₂z²w + a₃w² + a₄zw² + a₆w³`. This is the
characteristic equation derived from the Weierstrass equation by substituting
`x = z/w, y = -1/w` and multiplying by `-w³`. -/

/-- Unfolding `formalW_coeff` via `WellFounded.fix_eq`. -/
theorem formalW_coeff_eq_step (n : ℕ) :
    formalW_coeff W n = formalW_step W n (fun m _ ↦ formalW_coeff W m) := by
  show WellFoundedRelation.wf.fix (formalW_step W) n =
    formalW_step W n (fun m _ ↦ formalW_coeff W m)
  rw [WellFoundedRelation.wf.fix_eq]
  rfl

/-- The convolution `conv₂` of `formalW_coeff` with the truncation `m < n` agrees
    with the full convolution, since `formalW_coeff W k = 0` for `k < 3`. -/
theorem conv₂_truncate (n : ℕ) :
    conv₂ (fun m ↦ if m < n then formalW_coeff W m else 0) n =
      conv₂ (formalW_coeff W) n := by
  unfold conv₂
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
  show (if i < n then formalW_coeff W i else 0) *
       (if n - i < n then formalW_coeff W (n - i) else 0) =
       formalW_coeff W i * formalW_coeff W (n - i)
  rcases lt_or_eq_of_le hi with h_lt | h_eq
  · rw [if_pos h_lt]
    by_cases h_ni : n - i < n
    · rw [if_pos h_ni]
    · have h_i_eq_zero : i = 0 := by omega
      subst h_i_eq_zero
      rw [if_neg h_ni]
      rw [show formalW_coeff W 0 = 0 from formalW_coeff_zero W]
      ring
  · subst h_eq
    rw [if_neg (by omega : ¬ (i < i))]
    rw [show i - i = 0 from Nat.sub_self i]
    rw [show formalW_coeff W 0 = 0 from formalW_coeff_zero W]
    ring

/-- The conv₂ of formalW_coeff at index `n-1` equals the truncated version. -/
theorem conv₂_truncate' (n : ℕ) (hn : 1 ≤ n) :
    conv₂ (fun m ↦ if m < n then formalW_coeff W m else 0) (n - 1) =
      conv₂ (formalW_coeff W) (n - 1) := by
  unfold conv₂
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  show (if i < n then formalW_coeff W i else 0) *
       (if n - 1 - i < n then formalW_coeff W (n - 1 - i) else 0) =
       formalW_coeff W i * formalW_coeff W (n - 1 - i)
  have h_i_lt_n : i < n := by omega
  rw [if_pos h_i_lt_n]
  have h_ni_lt_n : n - 1 - i < n := by omega
  rw [if_pos h_ni_lt_n]

/-- `coeff n (formalW W * formalW W) = conv₂ (formalW_coeff W) n`. -/
theorem coeff_formalW_sq (n : ℕ) :
    PowerSeries.coeff n (formalW W * formalW W) = conv₂ (formalW_coeff W) n := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (M := R) (fun i j ↦ @PowerSeries.coeff R _ i (formalW W) *
                @PowerSeries.coeff R _ j (formalW W)) n]
  unfold conv₂
  apply Finset.sum_congr rfl
  intro i _
  show @PowerSeries.coeff R _ i (PowerSeries.mk (formalW_coeff W)) *
       @PowerSeries.coeff R _ (n - i) (PowerSeries.mk (formalW_coeff W)) =
       formalW_coeff W i * formalW_coeff W (n - i)
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

/-- `coeff n ((formalW W)^2) = conv₂ (formalW_coeff W) n`. -/
theorem coeff_formalW_pow_two (n : ℕ) :
    PowerSeries.coeff n ((formalW W) ^ 2) = conv₂ (formalW_coeff W) n := by
  rw [sq]; exact coeff_formalW_sq W n

/-- `coeff n (formalW W * (formalW W * formalW W)) = conv₃ (formalW_coeff W) n`. -/
theorem coeff_formalW_cube (n : ℕ) :
    PowerSeries.coeff n (formalW W * (formalW W * formalW W)) =
      conv₃ (formalW_coeff W) n := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (M := R) (fun i j ↦ @PowerSeries.coeff R _ i (formalW W) *
                @PowerSeries.coeff R _ j (formalW W * formalW W)) n]
  unfold conv₃
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_formalW_sq]
  show @PowerSeries.coeff R _ i (PowerSeries.mk (formalW_coeff W)) *
       conv₂ (formalW_coeff W) (n - i) = _
  rw [PowerSeries.coeff_mk]
  unfold conv₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `coeff n ((formalW W)^3) = conv₃ (formalW_coeff W) n`. -/
theorem coeff_formalW_pow_three (n : ℕ) :
    PowerSeries.coeff n ((formalW W) ^ 3) = conv₃ (formalW_coeff W) n := by
  have h : ((formalW W) ^ 3 : PowerSeries R) = formalW W * (formalW W * formalW W) := by
    rw [pow_succ, sq]
    exact mul_comm _ _
  rw [h]
  exact coeff_formalW_cube W n

/-- A single term of the `conv₃_truncate` triple sum: for indices `i ≤ n` and
    `j ≤ n - i`, truncating the three `formalW_coeff` factors at level `n` does not
    change the product, because `formalW_coeff W 0 = 0` absorbs the only index
    (namely `0`) that can fall outside the truncation range. -/
private theorem conv₃_truncate_term {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n - i) :
    (if i < n then formalW_coeff W i else 0) *
        (if j < n then formalW_coeff W j else 0) *
        (if n - i - j < n then formalW_coeff W (n - i - j) else 0) =
      formalW_coeff W i * formalW_coeff W j * formalW_coeff W (n - i - j) := by
  rcases lt_or_eq_of_le hi with h_i_lt | h_i_eq
  · rw [if_pos h_i_lt]
    rcases lt_or_eq_of_le hj with h_j_lt | h_j_eq
    · -- j ≤ n - i and j < n - i, so j < n
      have h_j_lt_n : j < n := by omega
      rw [if_pos h_j_lt_n]
      by_cases h_k_lt_n : n - i - j < n
      · rw [if_pos h_k_lt_n]
      · -- n - i - j ≥ n means i + j = 0
        have h_i_eq_zero : i = 0 := by omega
        have h_j_eq_zero : j = 0 := by omega
        subst h_i_eq_zero
        subst h_j_eq_zero
        rw [if_neg h_k_lt_n]
        rw [show formalW_coeff W 0 = 0 from formalW_coeff_zero W]
        ring
    · -- j = n - i
      subst h_j_eq
      -- n - i - (n - i) = 0
      rw [show n - i - (n - i) = 0 from Nat.sub_self _]
      rw [show formalW_coeff W 0 = 0 from formalW_coeff_zero W]
      split_ifs <;> ring
  · -- i = n
    subst h_i_eq
    -- j ≤ n - n = 0, so j = 0
    have h_j_eq_zero : j = 0 := by omega
    subst h_j_eq_zero
    rw [if_neg (by omega : ¬ (i < i))]
    rw [show formalW_coeff W 0 = 0 from formalW_coeff_zero W]
    ring

/-- The convolution `conv₃` of `formalW_coeff` with truncation agrees with the full version,
    since `formalW_coeff W k = 0` for `k < 3`. -/
theorem conv₃_truncate (n : ℕ) :
    conv₃ (fun m ↦ if m < n then formalW_coeff W m else 0) n =
      conv₃ (formalW_coeff W) n := by
  unfold conv₃
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
  exact conv₃_truncate_term W hi hj

/-- **Silverman IV.1.1**: The defining recurrence for `formalW W` as a `PowerSeries`
    identity.

    `w(z) = z³ + a₁zw(z) + a₂z²w(z) + a₃w(z)² + a₄zw(z)² + a₆w(z)³`

    This is the characteristic equation derived from the Weierstrass equation by
    substituting `x = z/w, y = -1/w` and multiplying through by `-w³`. The proof
    proceeds coefficient-by-coefficient: unfold `formalW_coeff` via `WellFounded.fix_eq`
    and match the resulting `formalW_step` formula with the polynomial expansion of
    the RHS using `coeff_mul`, `coeff_X_pow_mul`, and the convolution helpers. -/
theorem formalW_recurrence :
    formalW W =
      PowerSeries.X ^ 3 +
        @PowerSeries.C R _ W.a₁ * PowerSeries.X * formalW W +
        @PowerSeries.C R _ W.a₂ * PowerSeries.X ^ 2 * formalW W +
        @PowerSeries.C R _ W.a₃ * (formalW W) ^ 2 +
        @PowerSeries.C R _ W.a₄ * PowerSeries.X * (formalW W) ^ 2 +
        @PowerSeries.C R _ W.a₆ * (formalW W) ^ 3 := by
  -- Strategy: prove coefficient-by-coefficient. The LHS coefficient unfolds via
  -- WellFounded.fix_eq + formalW_step. The RHS coefficient is computed using
  -- the helpers coeff_formalW_pow_two, coeff_formalW_pow_three.
  ext n
  -- Step 1: compute the RHS coefficient
  have hRHS : @PowerSeries.coeff R _ n
      (PowerSeries.X ^ 3 +
        @PowerSeries.C R _ W.a₁ * PowerSeries.X * formalW W +
        @PowerSeries.C R _ W.a₂ * PowerSeries.X ^ 2 * formalW W +
        @PowerSeries.C R _ W.a₃ * (formalW W) ^ 2 +
        @PowerSeries.C R _ W.a₄ * PowerSeries.X * (formalW W) ^ 2 +
        @PowerSeries.C R _ W.a₆ * (formalW W) ^ 3) =
    (if n = 3 then 1 else 0) +
      W.a₁ * (if 1 ≤ n then formalW_coeff W (n - 1) else 0) +
      W.a₂ * (if 2 ≤ n then formalW_coeff W (n - 2) else 0) +
      W.a₃ * conv₂ (formalW_coeff W) n +
      W.a₄ * (if 1 ≤ n then conv₂ (formalW_coeff W) (n - 1) else 0) +
      W.a₆ * conv₃ (formalW_coeff W) n := by
    rw [show (@PowerSeries.C R _ W.a₁ * PowerSeries.X * formalW W : PowerSeries R) =
          @PowerSeries.C R _ W.a₁ * (PowerSeries.X * formalW W) from mul_assoc _ _ _,
        show (@PowerSeries.C R _ W.a₂ * PowerSeries.X ^ 2 * formalW W : PowerSeries R) =
          @PowerSeries.C R _ W.a₂ * (PowerSeries.X ^ 2 * formalW W) from mul_assoc _ _ _,
        show (@PowerSeries.C R _ W.a₄ * PowerSeries.X * (formalW W) ^ 2 : PowerSeries R) =
          @PowerSeries.C R _ W.a₄ * (PowerSeries.X * (formalW W) ^ 2) from mul_assoc _ _ _]
    rw [map_add, map_add, map_add, map_add, map_add]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_X_pow]
    rw [coeff_formalW_pow_two W n, coeff_formalW_pow_three W n]
    rw [show (PowerSeries.X * formalW W : PowerSeries R) = PowerSeries.X ^ 1 * formalW W from by
          rw [pow_one]]
    rw [show (PowerSeries.X * (formalW W) ^ 2 : PowerSeries R)
          = PowerSeries.X ^ 1 * (formalW W) ^ 2 from by rw [pow_one]]
    rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_X_pow_mul']
    -- Now: simplify coeff (n - k) (formalW W) = formalW_coeff W (n - k)
    -- and coeff (n - 1) ((formalW W)^2) = conv₂ ... (n - 1)
    rw [show @PowerSeries.coeff R _ (n - 1) (formalW W)
          = formalW_coeff W (n - 1) from by
        show @PowerSeries.coeff R _ (n - 1) (PowerSeries.mk (formalW_coeff W)) = _
        rw [PowerSeries.coeff_mk]]
    rw [show @PowerSeries.coeff R _ (n - 2) (formalW W)
          = formalW_coeff W (n - 2) from by
        show @PowerSeries.coeff R _ (n - 2) (PowerSeries.mk (formalW_coeff W)) = _
        rw [PowerSeries.coeff_mk]]
    rw [coeff_formalW_pow_two W (n - 1)]
  -- Step 2: rewrite the LHS coefficient via formalW_coeff_eq_step
  show @PowerSeries.coeff R _ n (formalW W) = _
  conv_lhs =>
    rw [show formalW W = PowerSeries.mk (formalW_coeff W) from rfl, PowerSeries.coeff_mk,
        formalW_coeff_eq_step W n]
  rw [hRHS]
  -- Step 3: case analysis on n
  unfold formalW_step
  -- Beta-reduce the inner lambda and convert dite to ite
  dsimp only
  simp only [dite_eq_ite]
  by_cases hn3 : n < 3
  · -- n < 3 case: LHS = 0
    rw [if_pos hn3]
    -- RHS: all terms vanish
    have h1 : ¬ (n = 3) := by omega
    rw [if_neg h1]
    interval_cases n
    all_goals
      simp [conv₂, conv₃, formalW_coeff_zero, formalW_coeff_one, formalW_coeff_two,
            Finset.sum_range_succ]
  · push Not at hn3
    rw [if_neg (not_lt.mpr hn3)]
    by_cases hn_eq3 : n = 3
    · -- n = 3 case: LHS = 1
      rw [if_pos hn_eq3]
      subst hn_eq3
      simp only []
      have h1 : (1 : ℕ) ≤ 3 := by norm_num
      have h2 : (2 : ℕ) ≤ 3 := by norm_num
      rw [if_pos h1, if_pos h2, if_pos h1]
      rw [show formalW_coeff W (3 - 1) = formalW_coeff W 2 from by norm_num,
          show formalW_coeff W (3 - 2) = formalW_coeff W 1 from by norm_num,
          formalW_coeff_one W, formalW_coeff_two W]
      simp [conv₂, conv₃, formalW_coeff_zero, formalW_coeff_one, formalW_coeff_two,
            Finset.sum_range_succ]
    · -- n ≥ 4 case
      rw [if_neg hn_eq3]
      have hn4 : 4 ≤ n := by omega
      rw [if_neg hn_eq3]
      rw [if_pos (show 1 ≤ n from by omega), if_pos (show 2 ≤ n from by omega),
          if_pos (show 1 ≤ n from by omega)]
      -- Use conv₂_truncate, conv₃_truncate for the LHS
      rw [conv₂_truncate W n, conv₂_truncate' W n (by omega), conv₃_truncate W n]
      -- The truncated w(n-1) and w(n-2) become formalW_coeff (already beta-reduced)
      rw [show (if n - 1 < n then formalW_coeff W (n - 1) else 0) = formalW_coeff W (n - 1) from
            if_pos (by omega)]
      rw [show (if n - 2 < n then formalW_coeff W (n - 2) else 0) = formalW_coeff W (n - 2) from
            if_pos (by omega)]
      ring

/-! ### Uniqueness of `formalW` (Silverman IV.1.1(b))

Uniqueness of `formalW` follows the factoring pattern: if `d := w' - formalW W`,
then `d = K · d` for some `K` with zero constant coefficient, hence `d = 0`
by `PowerSeries.eq_zero_of_self_eq_mul_self`
(see `HasseWeil/PowerSeriesHelpers.lean`).

**Status**: infrastructure ready (`eq_zero_of_self_eq_mul_self`), but the
factoring step `RHS(w') − RHS(formalW W) = K · d` cannot be established by
`ring`/`linear_combination`/`abel` because of a `PowerSeries R` typeclass
gap: `RightDistribClass (PowerSeries R)` and `IsRightCancelAdd (PowerSeries R)`
fail to synthesize in Lean 4.29 / mathlib v4.29.0-rc6, blocking the ring
tactic on distributivity-heavy identities. The factoring works on simple
identities in isolation but stops mid-normalisation on the multi-term
combination needed here. A coefficient-induction route (via
`PowerSeries.ext` and strong induction on `n`, using `coeff_mul`) avoids
the ring issue and is the recommended next step.
-/

end HasseWeil

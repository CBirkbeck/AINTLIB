import HasseWeil.FormalGroup.Definition
import HasseWeil.FormalGroup.PDeriv
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Invariant Differential for Formal Groups (Silverman IV.4)

For a formal group `F(X, Y)` over a commutative ring `R`, we define:

* `dX_at_zero F` — the power series `F_X(0, T)`, where `F_X` denotes
  the formal partial derivative of `F` with respect to its first variable. This is
  the power series whose `n`-th coefficient is the coefficient of `X¹Yⁿ` in `F(X,Y)`.

* `invariantDiff F` — the **normalized invariant differential**
  `ω_F = F_X(0, T)⁻¹ dT`. Since `F_X(0, 0) = 1` (a consequence of `F(X, 0) = X`),
  the series `F_X(0, T)` is a unit in `R⟦T⟧`, making the inverse well-defined.

The key result is **Corollary IV.4.3**: for a formal group homomorphism `f : F → G`,
the pullback of `ω_G` along `f` satisfies `ω_G ∘ f = f'(0) · ω_F`. This
connects the formal group coefficient (the linear term of `f`) to the pullback of
the invariant differential, and is the formal-group analogue of the curve-level
identity `φ*(ω) = a_φ · ω`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.4 (Prop. 4.2, Cor. 4.3)
-/

open MvPowerSeries

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-! ### F_X(0, T): the partial derivative at zero -/

/-- `F_X(0, T)`: the formal partial derivative of `F(X, Y)` with respect to `X`,
evaluated at `X = 0`. Concretely, this is the power series whose `n`-th coefficient
is the coefficient of `X¹Yⁿ` in `F(X, Y)`.

Since `F(X, 0) = X` (left unit), the constant coefficient is `1`.

Reference: Silverman IV.4, proof of Prop. 4.2. -/
noncomputable def FormalGroup.dX_at_zero (F : FormalGroup R) : PowerSeries R :=
  PowerSeries.mk fun n ↦
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
      F.toSeries

/-- The constant coefficient of `F_X(0, T)` is `1`.

The coefficient of `X¹Y⁰` in `F(X, Y)` is `1` because `F(X, 0) = X`
implies that the `X¹`-coefficient of `F` (at `Y = 0`) equals `1`. -/
theorem FormalGroup.dX_at_zero_constantCoeff (F : FormalGroup R) :
    @PowerSeries.constantCoeff R _ F.dX_at_zero = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, dX_at_zero, PowerSeries.coeff_mk]
  -- Goal: coeff (single 0 1 + single 1 0) F.toSeries = 1
  simp only [Finsupp.single_zero, add_zero]
  -- Goal: coeff (single 0 1) F.toSeries = 1
  -- Extract the coefficient at (single 0 1) from F.lunit : subst ![X 0, 0] F.toSeries = X 0
  have key := congr_arg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) F.lunit
  rw [MvPowerSeries.coeff_index_single_self_X] at key
  -- key : coeff (single 0 1) (subst ![X 0, 0] F.toSeries) = 1
  -- Expand the substitution using coeff_subst and isolate the d = single 0 1 term.
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  rw [MvPowerSeries.coeff_subst ha] at key
  rw [finsum_eq_single _ (Finsupp.single (0 : Fin 2) 1)] at key
  · -- At d = single 0 1 the product is (X 0)^1 and the coefficient is 1.
    simp only [Finsupp.prod_single_index, pow_zero, pow_one, Matrix.cons_val_zero] at key
    rw [MvPowerSeries.coeff_index_single_self_X, smul_eq_mul, mul_one] at key
    exact key
  · -- Every other multi-index d ≠ single 0 1 contributes 0.
    intro d hd
    suffices h : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
        (d.prod fun s e ↦ (![MvPowerSeries.X 0, (0 : MvPowerSeries (Fin 2) R)] s) ^ e) = 0 by
      rw [h, smul_zero]
    rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> simp),
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
    by_cases hd1 : d 1 = 0
    · -- Variable 1 has exponent 0: product is (X 0)^(d 0), but d 0 ≠ 1.
      simp only [hd1, pow_zero, mul_one]
      rw [MvPowerSeries.coeff_X_pow]
      have hd0 : d 0 ≠ 1 :=
        fun h01 ↦ hd (Finsupp.ext (fun i ↦ by fin_cases i <;> simp [h01, hd1]))
      split_ifs with h
      · exact absurd (by simpa [Finsupp.single_eq_same] using
            (DFunLike.congr_fun h 0).symm) hd0
      · rfl
    · -- Variable 1 has positive exponent: 0^(d 1) kills the product.
      rw [zero_pow hd1, mul_zero, map_zero]

/-- `F_X(0, T)` is a unit in `R⟦T⟧`. -/
theorem FormalGroup.dX_at_zero_isUnit (F : FormalGroup R) :
    IsUnit (F.dX_at_zero) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, F.dX_at_zero_constantCoeff]
  exact isUnit_one

/-! ### The normalized invariant differential -/

/-- The **normalized invariant differential** of a formal group `F`:
`ω_F = F_X(0, T)⁻¹ ∈ R⟦T⟧`.

This power series has constant coefficient `1` and satisfies the invariance
property `ω(F(T, S)) · F_T(T, S) = ω(T)` (Silverman Prop. IV.4.2).

In the elliptic curve context, this corresponds to the invariant differential
`dx/(2y + a₁x + a₃)` expanded as a power series in the local parameter
`t = -x/y` at the identity.

Reference: Silverman IV.4, Prop. 4.2. -/
noncomputable def FormalGroup.invariantDiff (F : FormalGroup R) : PowerSeries R :=
  PowerSeries.invOfUnit F.dX_at_zero 1

/-- `F_X(0, T) * ω_F = 1`. -/
@[simp]
theorem FormalGroup.dX_at_zero_mul_invariantDiff (F : FormalGroup R) :
    F.dX_at_zero * F.invariantDiff = 1 :=
  PowerSeries.mul_invOfUnit F.dX_at_zero 1
    (by rw [F.dX_at_zero_constantCoeff]; rfl)

/-- `ω_F * F_X(0, T) = 1`. -/
@[simp]
theorem FormalGroup.invariantDiff_mul_dX_at_zero (F : FormalGroup R) :
    F.invariantDiff * F.dX_at_zero = 1 :=
  PowerSeries.invOfUnit_mul F.dX_at_zero 1
    (by rw [F.dX_at_zero_constantCoeff]; rfl)

/-- The constant coefficient of `ω_F` is `1` (normalized). -/
@[simp]
theorem FormalGroup.invariantDiff_constantCoeff (F : FormalGroup R) :
    @PowerSeries.constantCoeff R _ F.invariantDiff = 1 := by
  rw [invariantDiff, PowerSeries.constantCoeff_invOfUnit]; rfl

/-! ### Corollary IV.4.3: Pullback of the invariant differential

For a formal group homomorphism `f : F → G` with `f(T) = c·T + O(T²)`,
the pullback of `ω_G` along `f` satisfies `ω_G(f(T)) · f'(T) = c · ω_F(T)`.

In particular, evaluating at `T = 0`: `f'(0) = c`, so
`ω_G ∘ f = f'(0) · ω_F`.

This is the formal-group analogue of `φ*(ω) = a_φ · ω` on elliptic curves. -/

variable {F G : FormalGroup R}

/-- `HasSubst` for a formal group homomorphism: the constant coefficient is zero,
hence nilpotent, so substitution is well-defined. -/
theorem FormalGroupHom.hasSubst (f : FormalGroupHom F G) :
    PowerSeries.HasSubst (S := R) f.toSeries :=
  PowerSeries.HasSubst.of_constantCoeff_zero' f.zero_const

/-- The intermediate chain rule identity for `dX_at_zero` (Silverman IV.4, Prop. 4.2).

For a formal group homomorphism `f : F → G` with `f(T) = c₁T + O(T²)`:
`f'(T) · F_X(0, T) = c₁ · G_X(0, f(T))`

This follows from differentiating `f(F(T,S)) = G(f(T), f(S))` with respect to `T`
and evaluating at `T = 0`. The LHS gives `f'(S) · F_X(0,S)` and the RHS gives
`c₁ · G_X(0, f(S))`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4, proof of Prop. 4.2. -/
-- Helper: substituting X_0 -> 0 preserves coefficients with X_0-degree 0.
-- That is, coeff_{single 1 n} (subst ![0, X 1] phi) = coeff_{single 1 n} phi.
private theorem coeff_subst_runit_eq (n : ℕ)
    (phi : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
      (MvPowerSeries.subst (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) phi) =
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) phi := by
  have ha : MvPowerSeries.HasSubst
      (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  rw [MvPowerSeries.coeff_subst ha]
  rw [finsum_eq_single _ (Finsupp.single (1 : Fin 2) n)]
  · -- At d = single 1 n: the product is (0^0 * (X 1)^n) = (X 1)^n.
    -- coeff at (single 1 n) of (X 1)^n = 1.
    rw [Finsupp.prod_single_index (by simp)]
    simp [Matrix.cons_val_one, MvPowerSeries.coeff_X_pow, smul_eq_mul]
  · -- For d ≠ single 1 n: the product has coeff 0 at (single 1 n).
    intro d hd
    suffices MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (d.prod fun s e ↦
          (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] s) ^ e) = 0 by
      rw [this, smul_zero]
    rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> simp),
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
    by_cases hd0 : d 0 = 0
    · simp only [hd0, pow_zero, one_mul, MvPowerSeries.coeff_X_pow]
      have hne : d 1 ≠ n :=
        fun h ↦ hd (Finsupp.ext (fun i ↦ by fin_cases i <;> simp [*, Finsupp.single_eq_same]))
      rw [if_neg (fun h ↦ hne ((Finsupp.single_injective (1 : Fin 2)).eq_iff.mp h).symm)]
    · rw [zero_pow hd0, zero_mul, map_zero]

-- Helper: coeff at (single 1 m) of F.toSeries equals [m = 1] (from runit: F(0,Y)=Y)
private theorem coeff_single1_F (F : FormalGroup R) (m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) m) F.toSeries =
      if m = 1 then 1 else 0 := by
  -- F.runit says subst ![0, X 1] F.toSeries = X 1.
  -- coeff_{single 1 m} (subst ![0, X 1] F) = coeff_{single 1 m} F (by coeff_subst_runit_eq).
  -- coeff_{single 1 m} (X 1) = [m = 1].
  rw [← coeff_subst_runit_eq, F.runit]
  rw [show (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) =
    (MvPowerSeries.X 1) ^ 1 from (pow_one _).symm, MvPowerSeries.coeff_X_pow]
  simp only [(Finsupp.single_injective (1 : Fin 2)).eq_iff]

-- Helper: coeff at (single 1 n) of F^k is [n = k]
-- (Since F(0,Y) = Y, we have F^k(0,Y) = Y^k)
private theorem coeff_runit_pow (F : FormalGroup R) (k n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
      (F.toSeries ^ k) = if n = k then 1 else 0 := by
  -- subst ![0, X 1] (F^k) = (X 1)^k (since subst is a ring hom and runit).
  rw [← coeff_subst_runit_eq]
  have ha : MvPowerSeries.HasSubst
      (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  rw [MvPowerSeries.subst_pow ha, F.runit, MvPowerSeries.coeff_X_pow]
  simp only [(Finsupp.single_injective (1 : Fin 2)).eq_iff]

-- Helper: coeff_1 of f^d is 0 when d ≥ 2 (since f has zero constant coeff)
private theorem coeff_one_pow_eq_zero {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    {d : ℕ} (hd : 2 ≤ d) :
    PowerSeries.coeff 1 (f ^ d) = 0 := by
  have : PowerSeries.X ^ d ∣ f ^ d :=
    pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hf) d
  exact PowerSeries.X_pow_dvd_iff.mp this 1 (by omega)

-- Helper: coeff_1 of f^d is [d=1] * coeff_1 f
private theorem coeff_one_pow {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (d : ℕ) :
    PowerSeries.coeff 1 (f ^ d) = if d = 1 then PowerSeries.coeff 1 f else 0 := by
  by_cases hd : d = 1
  · simp [hd]
  · rw [if_neg hd]
    rcases d with _ | _ | d
    · simp only [pow_zero]
      show PowerSeries.coeff 1 (1 : PowerSeries R) = 0
      rw [PowerSeries.coeff_one, if_neg one_ne_zero]
    · omega
    · exact coeff_one_pow_eq_zero hf (by omega)

-- Helper: coeff of subst (X i) f at a multi-index e.
-- subst (X i) f = f(X_i), so coeff_e = coeff_{e i} f when e is supported on {i}, else 0.
private theorem coeff_subst_X0 (g : PowerSeries R) (a b : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) g) =
      if b = 0 then PowerSeries.coeff a g else 0 := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.coeff_subst ha]
  by_cases hb : b = 0
  · subst hb
    simp only [Finsupp.single_zero, add_zero]
    rw [finsum_eq_single _ a]
    · simp [MvPowerSeries.coeff_X_pow, smul_eq_mul]
    · intro d hd
      simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul]
      rw [if_neg (fun h ↦ hd ((Finsupp.single_injective (0 : Fin 2)).eq_iff.mp h).symm),
        mul_zero]
  · rw [if_neg hb]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rw [MvPowerSeries.coeff_X_pow]
    rw [if_neg]
    · exact smul_zero _
    · intro h
      have := DFunLike.congr_fun h 1
      simp [Finsupp.add_apply, Finsupp.single_eq_same] at this
      exact absurd this hb

private theorem coeff_subst_X1 (g : PowerSeries R) (a b : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
      (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) g) =
      if a = 0 then PowerSeries.coeff b g else 0 := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.coeff_subst ha]
  by_cases hab : a = 0
  · subst hab
    simp only [Finsupp.single_zero, zero_add]
    rw [finsum_eq_single _ b]
    · simp [MvPowerSeries.coeff_X_pow, smul_eq_mul]
    · intro d hd
      simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul]
      rw [if_neg (fun h ↦ hd ((Finsupp.single_injective (1 : Fin 2)).eq_iff.mp h).symm),
        mul_zero]
  · rw [if_neg hab]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rw [MvPowerSeries.coeff_X_pow]
    rw [if_neg]
    · exact smul_zero _
    · intro h
      have := DFunLike.congr_fun h 0
      simp [Finsupp.add_apply, Finsupp.single_eq_same] at this
      exact absurd this hab

-- Key decomposition: any e : Fin 2 →₀ ℕ equals single 0 (e 0) + single 1 (e 1).
private lemma finsupp_fin2_decompose (e : Fin 2 →₀ ℕ) :
    e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) := by
  ext i; fin_cases i <;> simp [Finsupp.add_apply]

-- Value of the surviving antidiagonal term in `coeff_10_prod_orthogonal`:
-- the product of the single-index coefficients of the substituted powers.
private lemma coeff_subst_X0_X1_single_mul (g : PowerSeries R) (d0 d1 n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
      (PowerSeries.subst (MvPowerSeries.X 0) (g ^ d0)) *
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
      (PowerSeries.subst (MvPowerSeries.X 1) (g ^ d1)) =
    PowerSeries.coeff 1 (g ^ d0) * PowerSeries.coeff n (g ^ d1) := by
  rw [show Finsupp.single (0 : Fin 2) 1 = Finsupp.single 0 1 + Finsupp.single 1 0
      from by simp,
      show Finsupp.single (1 : Fin 2) n = Finsupp.single 0 0 + Finsupp.single 1 n
      from by simp]
  rw [coeff_subst_X0, coeff_subst_X1]; simp

-- Orthogonality vanishing: any antidiagonal pair `(e1, e2)` summing to the
-- surviving index `(single 0 1, single 1 n)` but distinct from it contributes
-- a zero coefficient product. Case split on `e1 1` and `e2 0`; the only way both
-- vanish is `(e1, e2) = (single 0 1, single 1 n)`, contradicting `hne`.
private lemma coeff_subst_X0_X1_mul_eq_zero_of_ne (g : PowerSeries R) (d0 d1 n : ℕ)
    {e1 e2 : Fin 2 →₀ ℕ}
    (hmem : e1 + e2 = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
    (hne : (e1, e2) ≠ (Finsupp.single (0 : Fin 2) 1, Finsupp.single (1 : Fin 2) n)) :
    MvPowerSeries.coeff e1
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (g ^ d0)) *
      MvPowerSeries.coeff e2
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (g ^ d1)) = 0 := by
  rw [show e1 = Finsupp.single 0 (e1 0) + Finsupp.single 1 (e1 1)
      from finsupp_fin2_decompose e1,
      show e2 = Finsupp.single 0 (e2 0) + Finsupp.single 1 (e2 1)
      from finsupp_fin2_decompose e2]
  rw [coeff_subst_X0, coeff_subst_X1]
  by_cases h1 : e1 1 = 0
  · rw [if_pos h1]
    by_cases h2 : e2 0 = 0
    · -- Both e1 1 = 0 and e2 0 = 0: forces (e1, e2) = (single 0 1, single 1 n)
      exfalso; apply hne
      have h10 : e1 0 + e2 0 = 1 := by
        have := DFunLike.congr_fun hmem 0; simp [Finsupp.add_apply] at this; linarith
      have h1n : e1 1 + e2 1 = n := by
        have := DFunLike.congr_fun hmem 1; simp [Finsupp.add_apply] at this; linarith
      have he10 : e1 0 = 1 := by omega
      have he21 : e2 1 = n := by omega
      ext1
      · show e1 = Finsupp.single 0 1
        rw [finsupp_fin2_decompose e1, h1, he10]; simp
      · show e2 = Finsupp.single 1 n
        rw [finsupp_fin2_decompose e2, h2, he21]; simp
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

-- Orthogonality: coeff_{(1,n)} (f(X_0)^d0 * f(X_1)^d1) = coeff_1(f^d0) * coeff_n(f^d1)
set_option maxHeartbeats 800000 in
private theorem coeff_10_prod_orthogonal (g : PowerSeries R) (d0 d1 n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
      ((PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) g) ^ d0 *
       (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) g) ^ d1) =
    PowerSeries.coeff 1 (g ^ d0) * PowerSeries.coeff n (g ^ d1) := by
  have ha0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have ha1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  -- Rewrite (subst (X i) g)^d = subst (X i) (g^d)
  rw [← PowerSeries.subst_pow ha0, ← PowerSeries.subst_pow ha1]
  -- Expand product using coeff_mul over antidiagonal
  rw [MvPowerSeries.coeff_mul]
  -- Only the surviving term `(single 0 1, single 1 n)` contributes
  rw [← coeff_subst_X0_X1_single_mul g d0 d1 n]
  apply Finset.sum_eq_single (Finsupp.single 0 1, Finsupp.single 1 n)
  · -- Other terms vanish by orthogonality of X_0 and X_1 substitutions
    intro ⟨e1, e2⟩ hmem hne
    exact coeff_subst_X0_X1_mul_eq_zero_of_ne g d0 d1 n (Finset.mem_antidiagonal.mp hmem) hne
  · -- The target pair is in the antidiagonal
    intro hmem
    rw [Finset.mem_antidiagonal] at hmem
    exfalso; apply hmem
    ext i; fin_cases i <;> simp [Finsupp.add_apply]

-- Helper: Finsupp.prod of the substitution vector at d = explicit product over Fin 2.
private lemma prod_subst_vec (f : FormalGroupHom F G) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s e ↦
      (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f.toSeries,
         PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f.toSeries] s) ^ e) =
    (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f.toSeries) ^ (d 0) *
    (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f.toSeries) ^ (d 1) := by
  rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> simp), Fin.prod_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

-- Helper: HasSubst for the substitution vector ![subst X₀ f, subst X₁ f].
private lemma hasSubst_subst_vec (f : FormalGroupHom F G) :
    MvPowerSeries.HasSubst
      (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f.toSeries,
         PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f.toSeries] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s <;> (
    show MvPowerSeries.constantCoeff (PowerSeries.subst _ f.toSeries) = 0
    rw [PowerSeries.constantCoeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d; rcases d with _ | d
    · simp [f.zero_const]
    · simp [zero_pow (Nat.succ_ne_zero d)])

-- Helper: finsum over Fin 2 →₀ ℕ with d 0 = 1 condition reduces to finsum over ℕ.
-- The function `p` may depend on the full multi-index `d`, not just `d 1`.
private lemma finsum_fin2_reduce_full (p : (Fin 2 →₀ ℕ) → R) :
    (∑ᶠ d : Fin 2 →₀ ℕ, if d 0 = 1 then p d else 0) =
    ∑ᶠ k : ℕ, p (Finsupp.single 0 1 + Finsupp.single 1 k) := by
  -- Section s : ℕ → Fin 2 →₀ ℕ embeds ℕ as {d | d 0 = 1}.
  let ι : ℕ → Fin 2 →₀ ℕ := fun k ↦ Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 k
  have hι0 : ∀ k, (ι k : Fin 2 →₀ ℕ) 0 = 1 := by intro k; simp [ι, Finsupp.add_apply]
  have hinj : Function.Injective ι := by
    intro a b hab
    have := DFunLike.congr_fun hab (1 : Fin 2)
    simp [ι, Finsupp.add_apply] at this; exact this
  have hmem : ∀ e : Fin 2 →₀ ℕ, e ∈ Set.range ι ↔ e 0 = 1 := by
    intro e; constructor
    · rintro ⟨k, rfl⟩; exact hι0 k
    · intro he0; exact ⟨e 1, Finsupp.ext fun i ↦ by fin_cases i <;> simp [ι, Finsupp.add_apply, he0]⟩
  have key : ∀ d : Fin 2 →₀ ℕ, (if d 0 = 1 then p d else (0 : R)) =
      Set.indicator (Set.range ι) (fun d ↦ if d 0 = 1 then p d else 0) d := by
    intro d; classical rw [Set.indicator_apply]
    by_cases hd : d ∈ Set.range ι
    · rw [if_pos hd]
    · rw [if_neg hd, if_neg (mt (hmem d).mpr hd)]
  conv_lhs => arg 1; ext d; rw [key d]
  rw [← finsum_mem_def, ← finsum_subtype_eq_finsum_cond (· ∈ Set.range ι)]
  rw [← finsum_comp_equiv (Equiv.ofInjective ι hinj)]
  congr 1; ext k
  show (if (ι k : Fin 2 →₀ ℕ) 0 = 1 then p (ι k) else 0) =
    p (Finsupp.single 0 1 + Finsupp.single 1 k)
  rw [if_pos (hι0 k)]

-- Helper: c * finsum f = finsum (c * f ·) when f has finite support.
private lemma mul_finsum_of_support_subset {α : Type*} (c : R) (f : α → R)
    {s : Finset α} (hs : Function.support f ⊆ ↑s) :
    c * (∑ᶠ a, f a) = ∑ᶠ a, c * f a := by
  rw [finsum_eq_finsetSum_of_support_subset f hs,
      finsum_eq_finsetSum_of_support_subset (fun a ↦ c * f a)
        (Function.support_subset_iff'.mpr fun a ha ↦
          by simp [Function.support_subset_iff'.mp hs a ha]),
      Finset.mul_sum]

-- RHS computation: coeff_{(1,n)} of G(f(X_0), f(X_1))
-- = c1 * coeff_n (subst f dG)
set_option maxHeartbeats 3200000 in
private theorem coeff_10_rhs (F G : FormalGroup R) (f : FormalGroupHom F G) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
      (MvPowerSeries.subst
        (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f.toSeries,
           PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f.toSeries] :
          Fin 2 → MvPowerSeries (Fin 2) R) G.toSeries) =
    PowerSeries.coeff 1 f.toSeries *
      PowerSeries.coeff n (PowerSeries.subst f.toSeries G.dX_at_zero) := by
  -- Step 1: Expand using MvPowerSeries.coeff_subst
  have ha := hasSubst_subst_vec f
  rw [MvPowerSeries.coeff_subst ha]
  -- Step 2: Simplify the product and apply orthogonality + coeff_one_pow
  simp_rw [prod_subst_vec f, coeff_10_prod_orthogonal, coeff_one_pow f.zero_const, smul_eq_mul]
  simp_rw [ite_mul, zero_mul, mul_ite, mul_zero]
  -- Goal: finsum d, if d 0 = 1 then coeff_d G * (c₁ * coeff_n(f^(d 1))) else 0
  --     = c₁ * coeff_n(subst f dXG)
  -- Step 3: Rearrange each ite branch
  conv_lhs =>
    arg 1; ext d
    rw [show (if d 0 = 1 then MvPowerSeries.coeff d G.toSeries *
          (PowerSeries.coeff 1 f.toSeries * PowerSeries.coeff n (f.toSeries ^ d 1))
        else 0) =
        if d 0 = 1 then PowerSeries.coeff 1 f.toSeries *
          (MvPowerSeries.coeff d G.toSeries * PowerSeries.coeff n (f.toSeries ^ d 1))
        else 0 from by split_ifs <;> ring]
  -- Step 4: Reduce finsum over Fin 2 →₀ ℕ to finsum over ℕ
  rw [finsum_fin2_reduce_full]
  -- Simplify Finsupp evaluations: (single 0 1 + single 1 k) 1 = k
  simp only [Finsupp.add_apply, Finsupp.single_apply, show (0 : Fin 2) ≠ 1 from by decide,
    ite_true, ite_false, zero_add]
  -- Goal: finsum k, c₁ * (coeff_{(1,k)} G * coeff_n(f^k)) = c₁ * coeff_n(subst f dXG)
  -- Step 5: Expand the RHS using PowerSeries.coeff_subst'
  rw [PowerSeries.coeff_subst' f.hasSubst]
  simp_rw [FormalGroup.dX_at_zero, PowerSeries.coeff_mk, smul_eq_mul]
  -- Goal: finsum k, c₁ * (coeff_{(1,k)} G * coeff_n(f^k))
  --     = c₁ * finsum k, coeff_{(1,k)} G * coeff_n(f^k)
  -- Step 6: Factor c₁ out using mul_finsum with finite support
  symm
  -- Use finsum_eq_finsetSum_of_support_subset on both sides, then Finset.mul_sum
  have heq : ∀ d : ℕ,
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 d) G.toSeries *
        PowerSeries.coeff n (f.toSeries ^ d) =
      PowerSeries.coeff d G.dX_at_zero * PowerSeries.coeff n (f.toSeries ^ d) := by
    intro d; simp [FormalGroup.dX_at_zero, PowerSeries.coeff_mk]
  simp_rw [heq]
  -- Factor c₁ out of the finsum using finite support
  have hfs := PowerSeries.coeff_subst_finite f.hasSubst G.dX_at_zero (Finsupp.single () n)
  exact mul_finsum_of_support_subset _ _ (s := hfs.toFinset) fun d hd ↦ by
    rw [Finset.mem_coe, hfs.mem_toFinset, Function.mem_support, smul_eq_mul]
    rwa [Function.mem_support] at hd

-- Sub-lemma: in the antidiag sum for coeff_{(1,n)} (F * F^d), terms vanish
-- unless (e1 0 = 0 and e1 1 = 1) or (e1 0 = 1 and e2 1 = d).
set_option maxHeartbeats 1600000 in
private theorem antidiag_term_vanish (F : FormalGroup R) (d n : ℕ)
    (e1 e2 : Fin 2 →₀ ℕ)
    (hsum : e1 + e2 = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
    (hA : ¬(e1 0 = 0 ∧ e1 1 = 1))
    (hB : ¬(e1 0 = 1 ∧ e2 1 = d)) :
    MvPowerSeries.coeff e1 F.toSeries *
      MvPowerSeries.coeff e2 (F.toSeries ^ d) = 0 := by
  have h0 : e1 0 + e2 0 = 1 := by
    have := DFunLike.congr_fun hsum 0
    simp [Finsupp.add_apply, Finsupp.single_eq_same] at this
    exact this
  rcases Nat.eq_zero_or_pos (e1 0) with he10 | he10
  · have he1eq : e1 = Finsupp.single 1 (e1 1) := Finsupp.ext fun i ↦ by
      fin_cases i <;> simp_all [Finsupp.single_eq_same]
    rw [he1eq, coeff_single1_F, if_neg (fun h ↦ hA ⟨he10, h⟩), zero_mul]
  · have he20 : e2 0 = 0 := by omega
    have he2eq : e2 = Finsupp.single 1 (e2 1) := Finsupp.ext fun i ↦ by
      fin_cases i <;> simp_all [Finsupp.single_eq_same]
    rw [he2eq, coeff_runit_pow, if_neg (fun h ↦ hB ⟨by omega, h⟩), mul_zero]

-- Sub-lemma: coeff_{(1,n)} (F^d) = d * coeff_{n+1-d} (dX_at_zero F) when d ≤ n+1
set_option maxHeartbeats 6400000 in
private theorem coeff_10_FG_pow (F : FormalGroup R) :
    ∀ (d n : ℕ),
    MvPowerSeries.coeff
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
      (F.toSeries ^ d) =
    if d ≤ n + 1 then (d : R) * PowerSeries.coeff (n + 1 - d) F.dX_at_zero
    else 0 := by
  intro d
  induction d with
  | zero =>
    intro n
    simp only [pow_zero, Nat.zero_le, le_add_iff_nonneg_left, if_true,
      Nat.cast_zero, zero_mul, MvPowerSeries.coeff_one]
    rw [if_neg]; intro h
    exact absurd (DFunLike.congr_fun h 0) (by
      simp [Finsupp.add_apply, Finsupp.single_eq_same])
  | succ d ih =>
    intro n
    -- For d+1 > n+1, use direct vanishing from nilpotent coefficient
    by_cases hdn : d + 1 ≤ n + 1
    · -- d + 1 ≤ n + 1, i.e., d ≤ n
      rw [if_pos hdn]
      have hdn' : d ≤ n := by omega
      rw [pow_succ, mul_comm, MvPowerSeries.coeff_mul]
      -- The antidiag sum: Σ coeff_e1(F) * coeff_e2(F^d)
      -- Only two "good" pairs survive. All others vanish.
      -- Pair A: e1 = single 1 1, e2 = single 0 1 + single 1 (n-1)
      --   value: 1 * coeff_{(1,n-1)}(F^d) = ih d (n-1)
      -- Pair B: e1 = single 0 1 + single 1 (n-d), e2 = single 1 d
      --   value: coeff_{(1,n-d)} F * 1 = coeff_{n-d}(dxF)
      -- We handle separately whether n = 0 (pair A doesn't exist) or n ≥ 1.
      by_cases hn : n = 0
      · -- n = 0, d = 0: the sum reduces to a single term
        subst hn
        have hd0 : d = 0 := by omega
        subst hd0
        -- After subst, goal should be about coeff_{(1,0)} (F * 1) or similar
        -- After subst, goal:
        -- Σ_{p ∈ antidiag} coeff p.1 F * coeff p.2 (F^0) = ↑(0+1) * coeff_{0+1-(0+1)} dxF
        simp only [pow_zero, Nat.zero_add, Nat.sub_self, Nat.cast_one, one_mul]
        -- Goal: Σ_{x ∈ antidiag} coeff x.1 F * coeff x.2 1 = coeff_0 dxF
        -- The only nonzero term has x.2 = 0, so x.1 = single 0 1 + single 1 0.
        -- Use sum_eq_single to isolate it.
        rw [Finset.sum_eq_single (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 0, 0)]
        · simp only [MvPowerSeries.coeff_one, mul_one, Finsupp.single_zero, add_zero, ite_true]
          rw [FormalGroup.dX_at_zero, PowerSeries.coeff_mk]
          simp only [Finsupp.single_zero, add_zero]
        · intro ⟨e1, e2⟩ hmem hne
          rw [MvPowerSeries.coeff_one]
          split_ifs with h
          · subst h; exfalso; apply hne
            rw [Finset.mem_antidiagonal] at hmem
            ext1 <;> simp_all [add_zero]
          · exact mul_zero _
        · intro hmem; exfalso; apply hmem
          rw [Finset.mem_antidiagonal]; simp
      · -- n ≥ 1: both pair A and pair B contribute
        have hn1 : 1 ≤ n := by omega
        -- We need the sum to equal (d+1) * coeff_{n-d}(dxF)
        -- = d * coeff_{n-d}(dxF) + coeff_{n-d}(dxF)
        -- pair A contributes: coeff_{(1,n-1)}(F^d) = ih d (n-1)
        --   = d * coeff_{n-d}(dxF) [since (n-1)+1-d = n-d when d ≤ n, and d ≤ (n-1)+1 iff d ≤ n]
        -- pair B contributes: coeff_{(1,n-d)} F = coeff_{n-d}(dxF)
        -- Total: (d+1) * coeff_{n-d}(dxF) ✓
        -- First, show the sum equals pair A value + pair B value
        -- using sum_eq_add for two distinguished elements
        have hA_mem : (Finsupp.single (1 : Fin 2) 1,
            Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - 1)) ∈
            Finset.antidiagonal
              (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n) := by
          rw [Finset.mem_antidiagonal]; ext i; fin_cases i
          · simp [Finsupp.add_apply, Finsupp.single_eq_same]
          · simp [Finsupp.add_apply, Finsupp.single_eq_same]; omega
        have hB_mem : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - d),
            Finsupp.single (1 : Fin 2) d) ∈
            Finset.antidiagonal
              (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n) := by
          rw [Finset.mem_antidiagonal]; ext i; fin_cases i
          · simp [Finsupp.add_apply, Finsupp.single_eq_same]
          · simp [Finsupp.add_apply, Finsupp.single_eq_same]; omega
        have hAB_ne : (Finsupp.single (1 : Fin 2) 1,
            Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - 1)) ≠
            (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - d),
             Finsupp.single (1 : Fin 2) d) := by
          intro h; have := congr_arg Prod.fst h; simp only at this
          exact absurd (DFunLike.congr_fun this 0) (by
            simp [Finsupp.add_apply, Finsupp.single_eq_same])
        -- Compute pair A value
        have hA_val :
            MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F.toSeries *
            MvPowerSeries.coeff
              (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - 1))
              (F.toSeries ^ d) =
            (d : R) * PowerSeries.coeff (n - d) F.dX_at_zero := by
          rw [coeff_single1_F, if_pos rfl, one_mul, ih, if_pos (by omega : d ≤ n - 1 + 1)]
          have : n - 1 + 1 - d = n - d := by omega
          rw [this]
        -- Compute pair B value
        have hB_val :
            MvPowerSeries.coeff
              (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - d))
              F.toSeries *
            MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) d) (F.toSeries ^ d) =
            PowerSeries.coeff (n - d) F.dX_at_zero := by
          rw [coeff_runit_pow, if_pos rfl, mul_one, FormalGroup.dX_at_zero,
            PowerSeries.coeff_mk]
        -- The sum = A_val + B_val (all other terms vanish)
        -- We show this by computing that for every term in the antidiagonal,
        -- either it's pair A, pair B, or it's zero.
        have hsum_eq : ∑ p ∈ Finset.antidiagonal
            (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n),
            MvPowerSeries.coeff p.1 F.toSeries *
              MvPowerSeries.coeff p.2 (F.toSeries ^ d) =
            MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F.toSeries *
              MvPowerSeries.coeff
                (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - 1))
                (F.toSeries ^ d) +
            MvPowerSeries.coeff
              (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - d))
              F.toSeries *
              MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) d) (F.toSeries ^ d) := by
          -- Step 1: extract pair A
          rw [← Finset.add_sum_erase _
            (fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) ↦
              MvPowerSeries.coeff p.1 F.toSeries *
                MvPowerSeries.coeff p.2 (F.toSeries ^ d))
            hA_mem]
          congr 1
          -- Step 2: extract pair B from the erased sum
          rw [← Finset.add_sum_erase _
            (fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) ↦
              MvPowerSeries.coeff p.1 F.toSeries *
                MvPowerSeries.coeff p.2 (F.toSeries ^ d))
            (Finset.mem_erase.mpr ⟨hAB_ne.symm, hB_mem⟩)]
          -- Step 3: show the remaining sum is 0
          suffices hzero : ∀ p ∈ ((Finset.antidiagonal
              (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)).erase
              (Finsupp.single (1 : Fin 2) 1,
               Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - 1))).erase
              (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (n - d),
               Finsupp.single (1 : Fin 2) d),
              MvPowerSeries.coeff p.1 F.toSeries *
                MvPowerSeries.coeff p.2 (F.toSeries ^ d) = 0 by
            rw [Finset.sum_eq_zero hzero, add_zero]
          intro ⟨e1, e2⟩ he
          rw [Finset.mem_erase] at he
          obtain ⟨hneB, he'⟩ := he
          rw [Finset.mem_erase] at he'
          obtain ⟨hneA, hmem⟩ := he'
          rw [Finset.mem_antidiagonal] at hmem
          apply antidiag_term_vanish F d n e1 e2 hmem
          · -- Not pair A
            intro ⟨h10, h11⟩; apply hneA
            have h0sum := DFunLike.congr_fun hmem 0
            simp [Finsupp.add_apply, Finsupp.single_eq_same] at h0sum
            have h1sum := DFunLike.congr_fun hmem 1
            simp [Finsupp.add_apply, Finsupp.single_eq_same] at h1sum
            exact Prod.ext
              (Finsupp.ext fun i ↦ by fin_cases i <;>
                simp_all [Finsupp.single_eq_same])
              (Finsupp.ext fun i ↦ by fin_cases i <;>
                simp_all [Finsupp.add_apply, Finsupp.single_eq_same,
                  Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
                  Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]; omega)
          · -- Not pair B
            intro ⟨h10, h21⟩; apply hneB
            have h1sum := DFunLike.congr_fun hmem 1
            simp [Finsupp.add_apply, Finsupp.single_eq_same] at h1sum
            exact Prod.ext
              (Finsupp.ext fun i ↦ by fin_cases i <;>
                simp_all [Finsupp.add_apply, Finsupp.single_eq_same,
                  Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
                  Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]; omega)
              (Finsupp.ext fun i ↦ by
                fin_cases i
                · simp
                  have h0sum := DFunLike.congr_fun hmem 0
                  simp [Finsupp.add_apply, Finsupp.single_eq_same] at h0sum
                  omega
                · simp [Finsupp.single_eq_same, h21])
        -- The sum equals A_val + B_val = (d+1) * coeff_{n-d} dxF
        trans ((d : R) * PowerSeries.coeff (n - d) F.dX_at_zero +
          PowerSeries.coeff (n - d) F.dX_at_zero)
        · -- LHS = A_val + B_val
          have hgoal := hsum_eq; rw [hA_val, hB_val] at hgoal; exact hgoal
        · -- A_val + B_val = (d+1) * coeff_{n+1-(d+1)} dxF
          rw [show n + 1 - (d + 1) = n - d from by omega]; push_cast; ring
    · -- d + 1 > n + 1: coeff vanishes by nilpotent degree bound
      rw [if_neg hdn]
      apply MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1)
      · rw [pow_one, FG.constantCoeff_FG_toSeries]
      · rw [map_add]; simp only [Finsupp.degree_apply]
        rw [Finsupp.support_single _ (by norm_num : (1 : ℕ) ≠ 0)]
        simp only [Finset.sum_singleton, Finsupp.single_eq_same]
        by_cases hn0 : n = 0
        · subst hn0; simp; omega
        · rw [Finsupp.support_single _ hn0, Finset.sum_singleton,
            Finsupp.single_eq_same]; omega

/-- The explicit `Finset` sum that both sides of `coeff_10_lhs` reduce to:
`Σ_{k=0}^{n} (k+1) · coeff_{k+1}(f) · coeff_{n-k}(F_X(0,T))`. -/
private noncomputable def coeff_10_sum (F G : FormalGroup R) (f : FormalGroupHom F G)
    (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), (↑(k + 1) : R) * PowerSeries.coeff (k + 1) f.toSeries *
    PowerSeries.coeff (n - k) F.dX_at_zero

/-- LHS shaping for `coeff_10_lhs`: the coefficient of `X¹Yⁿ` in `f(F(X,Y))`
unfolds (via `coeff_subst` and `coeff_10_FG_pow`) to the explicit range sum
`coeff_10_sum`. The `d = 0` term drops out and the surviving terms are reindexed
by `k = d - 1`. -/
private theorem coeff_10_subst_eq_sum (F G : FormalGroup R) (f : FormalGroupHom F G)
    (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
      (PowerSeries.subst F.toSeries f.toSeries) =
    coeff_10_sum F G f n := by
  rw [coeff_10_sum]
  -- Expand LHS using PowerSeries.coeff_subst
  have haF : PowerSeries.HasSubst (S := R) F.toSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero (FG.constantCoeff_FG_toSeries F)
  rw [PowerSeries.coeff_subst haF]
  -- LHS = finsum d, coeff_d(f) • coeff_{(1,n)} (F^d)
  simp_rw [coeff_10_FG_pow F, smul_eq_mul]
  -- LHS = finsum d, coeff_d(f) * (if d ≤ n+1 then d * coeff_{n+1-d}(dxF) else 0)
  simp_rw [mul_ite, mul_zero]
  -- LHS = finsum d, if d ≤ n+1 then coeff_d(f) * (d * coeff_{n+1-d}(dxF)) else 0
  -- The finsum has finite support; only d ∈ {0, ..., n+1} contribute
  -- For d = 0: 0 * ... = 0, so d = 0 doesn't contribute
  -- For d ∈ {1, ..., n+1}: contributes coeff_d(f) * d * coeff_{n+1-d}(dxF)
  -- For d > n+1: if branch gives 0
  -- Reindex: let i = d - 1 (so d = i+1, i ∈ {0, ..., n})
  -- First, normalise the multiplication order inside the if
  conv_lhs =>
    arg 1; ext d
    rw [show (if d ≤ n + 1 then PowerSeries.coeff d f.toSeries *
          ((d : R) * PowerSeries.coeff (n + 1 - d) F.dX_at_zero) else 0) =
        (if d ≤ n + 1 then (d : R) * PowerSeries.coeff d f.toSeries *
          PowerSeries.coeff (n + 1 - d) F.dX_at_zero else 0)
      from by split_ifs <;> ring]
  -- Convert the finsum to a Finset.sum over range (n + 2)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 2))
    (fun d hd ↦ by
      rw [Function.mem_support, ne_eq] at hd
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra h; push Not at h
      exact hd (if_neg (by omega : ¬(d ≤ n + 1))))]
  -- Kill the d = 0 term (it contributes 0 since d = 0 gives 0 * ... = 0)
  rw [Finset.sum_range_succ' (n := n + 1)]
  simp only [Nat.cast_zero, zero_mul, Nat.sub_zero, le_add_iff_nonneg_left,
    Nat.zero_le, ite_true, add_zero]
  -- Simplify the if-then-else (always true for k in range)
  have hsimp : ∀ k ∈ Finset.range (n + 1),
      (if k + 1 ≤ n + 1
       then (↑(k + 1) : R) * PowerSeries.coeff (k + 1) f.toSeries *
         PowerSeries.coeff (n + 1 - (k + 1)) F.dX_at_zero
       else 0) =
      (↑(k + 1) : R) * PowerSeries.coeff (k + 1) f.toSeries *
        PowerSeries.coeff (n - k) F.dX_at_zero := by
    intro k hk; rw [Finset.mem_range] at hk
    rw [if_pos (by omega : k + 1 ≤ n + 1)]
    have : n + 1 - (k + 1) = n - k := by omega
    rw [this]
  rw [Finset.sum_congr rfl hsimp]

/-- RHS shaping for `coeff_10_lhs`: the `n`-th coefficient of `f'(T) · F_X(0,T)`
unfolds (via `coeff_mul` and `coeff_derivative`) to the explicit range sum
`coeff_10_sum`, matching the antidiagonal sum against `range (n+1)` through the
bijection `k ↦ (k, n - k)`. -/
private theorem coeff_derivative_mul_dX_eq_sum (F G : FormalGroup R)
    (f : FormalGroupHom F G) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative R f.toSeries * F.dX_at_zero) =
    coeff_10_sum F G f n := by
  rw [coeff_10_sum]
  -- Expand RHS using coeff_mul and coeff_derivative
  rw [PowerSeries.coeff_mul]
  -- = Σ_{(i,j) ∈ antidiag n} coeff_i(f') * coeff_j(dxF)
  simp_rw [PowerSeries.coeff_derivative]
  -- = Σ_{(i,j) ∈ antidiag n} (coeff_{i+1}(f) * (i+1)) * coeff_j(dxF)
  -- Match Σ_{k ∈ range(n+1)} ... against the antidiagonal via k <-> (k, n - k)
  refine (Finset.sum_nbij' (fun k ↦ (k, n - k)) (fun p ↦ p.1) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk; rw [Finset.mem_range] at hk
    rw [Finset.mem_antidiagonal]; omega
  · intro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    rw [Finset.mem_range]; omega
  · intro k _; rfl
  · intro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab; ext <;> simp; omega
  · intro k hk
    rw [Finset.mem_range] at hk
    change (↑(k + 1) : R) * PowerSeries.coeff (k + 1) f.toSeries *
        PowerSeries.coeff (n - k) F.dX_at_zero =
      PowerSeries.coeff (k + 1) f.toSeries * (↑k + 1) *
        PowerSeries.coeff (n - k) F.dX_at_zero
    push_cast; ring

-- LHS computation: coeff_{(1,n)} of f(F(X,Y))
-- = coeff_n (f' * dF)
private theorem coeff_10_lhs (F G : FormalGroup R) (f : FormalGroupHom F G) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n)
      (PowerSeries.subst F.toSeries f.toSeries) =
    PowerSeries.coeff n (PowerSeries.derivative R f.toSeries * F.dX_at_zero) :=
  (coeff_10_subst_eq_sum F G f n).trans (coeff_derivative_mul_dX_eq_sum F G f n).symm

theorem FormalGroup.dX_at_zero_chain (f : FormalGroupHom F G) :
    (PowerSeries.derivative R f.toSeries) * F.dX_at_zero =
      PowerSeries.C (PowerSeries.coeff 1 f.toSeries) *
        PowerSeries.subst f.toSeries G.dX_at_zero := by
  ext n
  -- Use preserves_add at multi-index (1, n)
  have key := congr_arg
    (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) n))
    f.preserves_add
  rw [coeff_10_lhs F G f n] at key
  rw [coeff_10_rhs F G f n] at key
  -- key : coeff_n (f' * dF) = c1 * coeff_n (subst f dG)
  rw [key, PowerSeries.coeff_C_mul]

/-- **Corollary IV.4.3** (chain rule for invariant differentials).

For a formal group homomorphism `f : F → G` with `f(T) = c₁T + O(T²)`:
`ω_G(f(T)) · f'(T) = c₁ · ω_F(T)`

where `ω_F = F_X(0,T)⁻¹` is the normalized invariant differential.

This is the formal-group analogue of `φ*(ω) = a_φ · ω` for elliptic curves
and connects the linear coefficient of a homomorphism to the pullback of the
invariant differential.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4, Corollary 4.3. -/
theorem FormalGroup.invariantDiff_chain (f : FormalGroupHom F G) :
    PowerSeries.subst f.toSeries G.invariantDiff *
      (PowerSeries.derivative R f.toSeries) =
    PowerSeries.C (PowerSeries.coeff 1 f.toSeries) * F.invariantDiff := by
  -- Set up abbreviations to ensure all terms are in PowerSeries R, avoiding
  -- MvPowerSeries Unit R / PowerSeries R defeq issues with rw/simp.
  set c₁ : PowerSeries R := PowerSeries.C (PowerSeries.coeff 1 f.toSeries)
  set ωG' : PowerSeries R := PowerSeries.subst f.toSeries G.invariantDiff
  set dG' : PowerSeries R := PowerSeries.subst f.toSeries G.dX_at_zero
  set f' : PowerSeries R := PowerSeries.derivative R f.toSeries
  set ωF : PowerSeries R := F.invariantDiff
  set dF : PowerSeries R := F.dX_at_zero
  -- The intermediate identity: f' * dF = c₁ * dG'
  have hdx : f' * dF = c₁ * dG' := F.dX_at_zero_chain f
  -- Substitution preserves the product ωG · dxG = 1
  have hsubst_prod : ωG' * dG' = 1 := by
    change PowerSeries.subst f.toSeries G.invariantDiff *
        PowerSeries.subst f.toSeries G.dX_at_zero = 1
    have hf := f.hasSubst
    rw [← PowerSeries.subst_mul hf, G.invariantDiff_mul_dX_at_zero]
    rw [show PowerSeries.subst f.toSeries =
        (PowerSeries.substAlgHom hf : PowerSeries R →ₐ[R] PowerSeries R)
        from (PowerSeries.coe_substAlgHom hf).symm]
    exact (PowerSeries.substAlgHom hf).map_one
  -- Cancel dX_at_zero F (a unit) from the right.
  -- Both sides, when multiplied by dF, equal c₁.
  apply F.dX_at_zero_isUnit.mul_right_cancel
  trans c₁
  · -- ωG' * f' * dF = ωG' * (f' * dF) = ωG' * (c₁ * dG')
    --              = c₁ * (ωG' * dG') = c₁ * 1 = c₁
    calc ωG' * f' * dF
        = ωG' * (f' * dF) := mul_assoc _ _ _
      _ = ωG' * (c₁ * dG') := congr_arg (ωG' * ·) hdx
      _ = c₁ * (ωG' * dG') := mul_left_comm _ _ _
      _ = c₁ * 1 := congr_arg (c₁ * ·) hsubst_prod
      _ = c₁ := mul_one _
  · -- c₁ * ωF * dF = c₁ * (ωF * dF) = c₁ * (dF * ωF) = c₁ * 1 = c₁
    exact (calc c₁ * ωF * dF
        = c₁ * (ωF * dF) := mul_assoc _ _ _
      _ = c₁ * (dF * ωF) := congr_arg (c₁ * ·) (mul_comm ωF dF)
      _ = c₁ * 1 := congr_arg (c₁ * ·) F.dX_at_zero_mul_invariantDiff
      _ = c₁ := mul_one _).symm

/-! ### Silverman IV.4.2: translation invariance of the invariant differential

We prove the **translation-invariance identity** for the invariant differential
of a formal group `F/R`:
`ω_F(F(T, S)) · F_X(T, S) = ω_F(T)` in `R⟦T, S⟧`,
where `F_X(T, S) = pderiv 0 F.toSeries` and `ω_F(F(T,S))` is the substitution
`PowerSeries.subst F.toSeries F.invariantDiff` (viewing `F.toSeries` as a
bivariate series).

The proof differentiates the associativity `F(F(X,Y),Z) = F(X,F(Y,Z))` with
respect to `X` and specializes to `X = 0`, following Silverman p. 120. -/

namespace FormalGroup

/-- The substitution `![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) R`
(Silverman's `(X, Y)` slot of associativity). -/
private noncomputable def pairXY (R : Type*) [CommRing R] :
    Fin 2 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0, MvPowerSeries.X 1]

/-- The substitution `![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) R`
(Silverman's `(Y, Z)` slot of associativity). -/
private noncomputable def pairYZ (R : Type*) [CommRing R] :
    Fin 2 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 1, MvPowerSeries.X 2]

/-- The "left" outer substitution of associativity, `(F(X,Y), Z)`. -/
private noncomputable def assocL (F : FormalGroup R) :
    Fin 2 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.subst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries,
    MvPowerSeries.X 2]

/-- The "right" outer substitution of associativity, `(X, F(Y,Z))`. -/
private noncomputable def assocR (F : FormalGroup R) :
    Fin 2 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0,
    MvPowerSeries.subst (pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries]

/-- The specialization `Fin 3 → MvPowerSeries (Fin 2) R` sending
`0 ↦ 0, 1 ↦ X 0, 2 ↦ X 1`. Collapses a `Fin 3` identity to a `Fin 2` identity
by setting the first variable to zero. -/
private noncomputable def shift3to2 (R : Type*) [CommRing R] :
    Fin 3 → MvPowerSeries (Fin 2) R :=
  ![0, MvPowerSeries.X 0, MvPowerSeries.X 1]

private lemma hasSubst_pairXY :
    MvPowerSeries.HasSubst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s <;> simp [pairXY]

private lemma hasSubst_pairYZ :
    MvPowerSeries.HasSubst (pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s <;> simp [pairYZ]

private lemma hasSubst_assocL (F : FormalGroup R) :
    MvPowerSeries.HasSubst (assocL F) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s
  · show MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R)
        F.toSeries) = 0
    exact MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_pairXY
      (fun i ↦ by fin_cases i <;> simp [pairXY])
      (FG.constantCoeff_FG_toSeries F)
  · show MvPowerSeries.constantCoeff
      (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) = 0
    simp

private lemma hasSubst_assocR (F : FormalGroup R) :
    MvPowerSeries.HasSubst (assocR F) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s
  · show MvPowerSeries.constantCoeff
      (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) = 0
    simp
  · show MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R)
        F.toSeries) = 0
    exact MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_pairYZ
      (fun i ↦ by fin_cases i <;> simp [pairYZ])
      (FG.constantCoeff_FG_toSeries F)

private lemma hasSubst_shift3to2 :
    MvPowerSeries.HasSubst (shift3to2 R : Fin 3 → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s <;> simp [shift3to2]

/-! #### Simplifying the partial derivative of each side of associativity -/

/-- The partial derivative of the LHS of associativity w.r.t. the first variable,
simplified via the chain rule. -/
private lemma pderiv_subst_assocL (F : FormalGroup R) :
    MvPowerSeries.pderiv (0 : Fin 3)
        (MvPowerSeries.subst (assocL F) F.toSeries) =
      MvPowerSeries.subst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R)
          (MvPowerSeries.pderiv 0 F.toSeries) *
        MvPowerSeries.subst (assocL F) (MvPowerSeries.pderiv 0 F.toSeries) := by
  rw [MvPowerSeries.pderiv_subst_fin2 0 (hasSubst_assocL F) F.toSeries]
  have h1 : MvPowerSeries.pderiv (0 : Fin 3) ((assocL F) 1) = 0 := by
    show MvPowerSeries.pderiv (0 : Fin 3)
      (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) = 0
    exact MvPowerSeries.pderiv_X_of_ne (by decide)
  have h0 : MvPowerSeries.pderiv (0 : Fin 3) ((assocL F) 0) =
      MvPowerSeries.subst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R)
        (MvPowerSeries.pderiv 0 F.toSeries) := by
    show MvPowerSeries.pderiv (0 : Fin 3)
      (MvPowerSeries.subst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R)
        F.toSeries) = _
    rw [MvPowerSeries.pderiv_subst_fin2 0 hasSubst_pairXY F.toSeries]
    have hX0 : MvPowerSeries.pderiv (0 : Fin 3)
        ((pairXY R : Fin 2 → MvPowerSeries (Fin 3) R) 0) = 1 := by
      show MvPowerSeries.pderiv (0 : Fin 3)
        (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) = 1
      exact MvPowerSeries.pderiv_X_self 0
    have hX1 : MvPowerSeries.pderiv (0 : Fin 3)
        ((pairXY R : Fin 2 → MvPowerSeries (Fin 3) R) 1) = 0 := by
      show MvPowerSeries.pderiv (0 : Fin 3)
        (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) = 0
      exact MvPowerSeries.pderiv_X_of_ne (by decide)
    rw [hX0, hX1, one_mul, zero_mul, add_zero]
  rw [h0, h1, zero_mul, add_zero]

/-- The partial derivative of the RHS of associativity w.r.t. the first variable. -/
private lemma pderiv_subst_assocR (F : FormalGroup R) :
    MvPowerSeries.pderiv (0 : Fin 3)
        (MvPowerSeries.subst (assocR F) F.toSeries) =
      MvPowerSeries.subst (assocR F) (MvPowerSeries.pderiv 0 F.toSeries) := by
  rw [MvPowerSeries.pderiv_subst_fin2 0 (hasSubst_assocR F) F.toSeries]
  have h0 : MvPowerSeries.pderiv (0 : Fin 3) ((assocR F) 0) = 1 := by
    show MvPowerSeries.pderiv (0 : Fin 3)
      (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) = 1
    exact MvPowerSeries.pderiv_X_self 0
  have h1 : MvPowerSeries.pderiv (0 : Fin 3) ((assocR F) 1) = 0 := by
    show MvPowerSeries.pderiv (0 : Fin 3)
      (MvPowerSeries.subst (pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R)
        F.toSeries) = 0
    rw [MvPowerSeries.pderiv_subst_fin2 0 hasSubst_pairYZ F.toSeries]
    have hX1 : MvPowerSeries.pderiv (0 : Fin 3)
        ((pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R) 0) = 0 := by
      show MvPowerSeries.pderiv (0 : Fin 3)
        (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) R) = 0
      exact MvPowerSeries.pderiv_X_of_ne (by decide)
    have hX2 : MvPowerSeries.pderiv (0 : Fin 3)
        ((pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R) 1) = 0 := by
      show MvPowerSeries.pderiv (0 : Fin 3)
        (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) = 0
      exact MvPowerSeries.pderiv_X_of_ne (by decide)
    rw [hX1, hX2, zero_mul, zero_mul, add_zero]
  rw [h0, h1, one_mul, zero_mul, add_zero]

/-- The `Fin 3` identity obtained by differentiating `F.assoc` w.r.t. the first
variable. -/
private lemma pderiv_assoc_identity (F : FormalGroup R) :
    MvPowerSeries.subst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R)
        (MvPowerSeries.pderiv 0 F.toSeries) *
      MvPowerSeries.subst (assocL F) (MvPowerSeries.pderiv 0 F.toSeries) =
    MvPowerSeries.subst (assocR F) (MvPowerSeries.pderiv 0 F.toSeries) := by
  have h := congr_arg (MvPowerSeries.pderiv (0 : Fin 3)) F.assoc
  -- Rewrite both sides of h using assocL, assocR (which unfold to the raw assoc).
  rw [show MvPowerSeries.subst
        (![MvPowerSeries.subst
              (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
                Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries,
            MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R)
          F.toSeries =
      MvPowerSeries.subst (assocL F) F.toSeries from rfl,
      show MvPowerSeries.subst
        (![MvPowerSeries.X (0 : Fin 3),
            MvPowerSeries.subst
              (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries] :
          Fin 2 → MvPowerSeries (Fin 3) R)
          F.toSeries =
      MvPowerSeries.subst (assocR F) F.toSeries from rfl] at h
  rw [pderiv_subst_assocL, pderiv_subst_assocR] at h
  exact h

/-! #### Evaluating at `X = 0` via the `shift3to2` substitution -/

/-- `shift3to2 ∘ pairXY = ![0, X 0]`. -/
private lemma shift3to2_comp_pairXY :
    (fun s ↦ MvPowerSeries.subst (shift3to2 R : Fin 3 → MvPowerSeries (Fin 2) R)
      ((pairXY R : Fin 2 → MvPowerSeries (Fin 3) R) s)) =
      (![0, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
  funext s; fin_cases s
  · show MvPowerSeries.subst (shift3to2 R)
      ((pairXY R : Fin 2 → MvPowerSeries (Fin 3) R) 0) = _
    simp only [pairXY, Matrix.cons_val_zero]
    rw [MvPowerSeries.subst_X hasSubst_shift3to2 0]; rfl
  · show MvPowerSeries.subst (shift3to2 R)
      ((pairXY R : Fin 2 → MvPowerSeries (Fin 3) R) 1) = _
    simp only [pairXY, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [MvPowerSeries.subst_X hasSubst_shift3to2 1]; rfl

/-- `shift3to2 ∘ pairYZ = ![X 0, X 1]`. -/
private lemma shift3to2_comp_pairYZ :
    (fun s ↦ MvPowerSeries.subst (shift3to2 R : Fin 3 → MvPowerSeries (Fin 2) R)
      ((pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R) s)) =
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
  funext s; fin_cases s
  · show MvPowerSeries.subst (shift3to2 R)
      ((pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R) 0) = _
    simp only [pairYZ, Matrix.cons_val_zero]
    rw [MvPowerSeries.subst_X hasSubst_shift3to2 1]; rfl
  · show MvPowerSeries.subst (shift3to2 R)
      ((pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R) 1) = _
    simp only [pairYZ, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [MvPowerSeries.subst_X hasSubst_shift3to2 2]; rfl

/-- Variant of `F.runit`: `F(0, X 0) = X 0` (same as `F(0, X 1) = X 1`
after substituting `X 0` for `X 1`). -/
private lemma runit_at_X0 (F : FormalGroup R) :
    MvPowerSeries.subst
        (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] :
          Fin 2 → MvPowerSeries (Fin 2) R) F.toSeries =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) := by
  -- Apply `subst ![X 0, X 0]` to `F.runit : subst ![0, X 1] F = X 1`.
  have hb : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, MvPowerSeries.X 0] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  have ha : MvPowerSeries.HasSubst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  have happ := congr_arg (MvPowerSeries.subst
      (![MvPowerSeries.X 0, MvPowerSeries.X 0] :
        Fin 2 → MvPowerSeries (Fin 2) R)) F.runit
  rw [MvPowerSeries.subst_comp_subst_apply ha hb,
      MvPowerSeries.subst_X hb 1] at happ
  -- happ : subst (subst b ∘ ![0, X 1]) F = X 0.
  -- subst b ∘ ![0, X 1] evaluates to ![0, X 0].
  have hcomp : (fun s ↦ MvPowerSeries.subst
      (![MvPowerSeries.X 0, MvPowerSeries.X 0] :
        Fin 2 → MvPowerSeries (Fin 2) R)
      ((![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) s)) =
      (![0, MvPowerSeries.X 0] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    funext s; fin_cases s
    · show MvPowerSeries.subst
        (![MvPowerSeries.X 0, MvPowerSeries.X 0] :
          Fin 2 → MvPowerSeries (Fin 2) R) 0 = 0
      rw [← MvPowerSeries.substAlgHom_apply hb, map_zero]
    · show MvPowerSeries.subst
        (![MvPowerSeries.X 0, MvPowerSeries.X 0] :
          Fin 2 → MvPowerSeries (Fin 2) R)
        (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.X 0
      rw [MvPowerSeries.subst_X hb 1]; rfl
  rw [hcomp] at happ
  exact happ

/-- `shift3to2 ∘ assocL = ![X 0, X 1]`: after `X = 0`, `F(0, X 0) = X 0`. -/
private lemma shift3to2_comp_assocL (F : FormalGroup R) :
    (fun s ↦ MvPowerSeries.subst (shift3to2 R : Fin 3 → MvPowerSeries (Fin 2) R)
      ((assocL F) s)) =
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
  funext s; fin_cases s
  · show MvPowerSeries.subst (shift3to2 R)
      (MvPowerSeries.subst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R)
        F.toSeries) = _
    rw [MvPowerSeries.subst_comp_subst_apply hasSubst_pairXY hasSubst_shift3to2,
        shift3to2_comp_pairXY]
    exact F.runit_at_X0
  · show MvPowerSeries.subst (shift3to2 R)
      (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) R) = _
    rw [MvPowerSeries.subst_X hasSubst_shift3to2 2]; rfl

/-- `shift3to2 ∘ assocR = ![0, F.toSeries]`. -/
private lemma shift3to2_comp_assocR (F : FormalGroup R) :
    (fun s ↦ MvPowerSeries.subst (shift3to2 R : Fin 3 → MvPowerSeries (Fin 2) R)
      ((assocR F) s)) =
      (![0, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R) := by
  funext s; fin_cases s
  · show MvPowerSeries.subst (shift3to2 R)
      (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) R) = _
    rw [MvPowerSeries.subst_X hasSubst_shift3to2 0]; rfl
  · show MvPowerSeries.subst (shift3to2 R)
      (MvPowerSeries.subst (pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R)
        F.toSeries) = _
    rw [MvPowerSeries.subst_comp_subst_apply hasSubst_pairYZ hasSubst_shift3to2,
        shift3to2_comp_pairYZ]
    have h : (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 2) R) = MvPowerSeries.X := by
      funext s; fin_cases s <;> rfl
    rw [h]; exact congr_fun MvPowerSeries.subst_self F.toSeries

/-! #### The identification `F_X(0, T) = dX_at_zero(T)` -/

/-- Auxiliary: the coefficient of `e` in `(![0, X 0] : Fin 2 → MvPS (Fin 2) R)^d`
equals `coeff_e ((X 0)^(d 1))` if `d 0 = 0`, else 0. -/
private lemma coeff_prod_subst_vec_zero_X0 (d e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff (R := R) e
      (d.prod fun s n ↦
        (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] s) ^ n) =
      if d 0 = 0 then MvPowerSeries.coeff e
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ (d 1)) else 0 := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  by_cases hd0 : d 0 = 0
  · simp [hd0]
  · rw [zero_pow hd0, zero_mul, map_zero, if_neg hd0]

/-- Reindexing: a finsum over `d : Fin 2 →₀ ℕ` of a term that vanishes unless
`d 0 = 0` collapses to a finsum over `n : ℕ` along `n ↦ Finsupp.single 1 n`, the
map enumerating `{d | d 0 = 0}`. -/
private lemma finsum_ite_first_eq_zero_eq_finsum_single_one (g : (Fin 2 →₀ ℕ) → R) :
    (∑ᶠ d : Fin 2 →₀ ℕ, if d 0 = 0 then g d else 0) =
      ∑ᶠ n : ℕ, g (Finsupp.single (1 : Fin 2) n) := by
  classical
  symm
  let ι : ℕ → Fin 2 →₀ ℕ := fun n ↦ Finsupp.single (1 : Fin 2) n
  have hinj : Function.Injective ι := fun a b hab ↦ by
    have := DFunLike.congr_fun hab (1 : Fin 2)
    simp [ι] at this; exact this
  have himg : ∀ d : Fin 2 →₀ ℕ, d ∈ Set.range ι ↔ d 0 = 0 := by
    intro d; constructor
    · rintro ⟨n, rfl⟩
      simp [ι]
    · intro h0
      refine ⟨d 1, ?_⟩
      ext i; fin_cases i
      · simp [ι, h0]
      · simp [ι]
  -- Expand the LHS finsum as an indicator finsum, then pull back through `ι`.
  have key : ∀ d : Fin 2 →₀ ℕ,
      (if d 0 = 0 then g d else (0 : R)) = Set.indicator (Set.range ι) g d := by
    intro d; rw [Set.indicator_apply]
    split_ifs with h1 h2 h3
    · rfl
    · exfalso; exact h2 ((himg d).mpr h1)
    · exfalso; exact h1 ((himg d).mp h3)
    · rfl
  conv_rhs => arg 1; ext d; rw [key d]
  rw [← finsum_mem_def, ← finsum_subtype_eq_finsum_cond (· ∈ Set.range ι)]
  rw [← finsum_comp_equiv (Equiv.ofInjective ι hinj)]
  apply finsum_congr
  intro n
  have h1 : ((Equiv.ofInjective ι hinj n : Set.range ι) : Fin 2 →₀ ℕ) =
      Finsupp.single (1 : Fin 2) n := rfl
  rw [h1]

/-- The per-term coefficient match for `subst_zero_X0_pderiv0`: at index
`Finsupp.single 1 n`, the coefficient of `pderiv 0 F.toSeries` reproduces the
`n`-th coefficient of `F.dX_at_zero`, against the same `(X 0)^n` factor. -/
private lemma coeff_single_one_pderiv0_smul_eq_dX_at_zero (F : FormalGroup R)
    (e : Fin 2 →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (MvPowerSeries.pderiv 0 F.toSeries) •
        MvPowerSeries.coeff e
          ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ ((Finsupp.single (1 : Fin 2) n) 1)) =
      PowerSeries.coeff n F.dX_at_zero •
        MvPowerSeries.coeff e ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ n) := by
  rw [Finsupp.single_eq_same, MvPowerSeries.coeff_pderiv]
  -- coeff at (single 1 n) of pderiv 0 F = (0 + 1) • coeff_{single 1 n + single 0 1} F
  --                                     = coeff_{(1, n)}(F) [using (1, n) = single 0 1 + single 1 n].
  rw [show (Finsupp.single (1 : Fin 2) n : Fin 2 →₀ ℕ) 0 = 0 by
      rw [Finsupp.single_apply]; rfl,
    show Finsupp.single (1 : Fin 2) n + Finsupp.single 0 1 =
        Finsupp.single 0 1 + Finsupp.single 1 n by rw [add_comm]]
  -- Match with the `dX_at_zero` formula.
  rw [FormalGroup.dX_at_zero, PowerSeries.coeff_mk]
  simp

/-- Silverman's identity `F_X(0, T) = dX_at_zero(T)`. -/
private lemma subst_zero_X0_pderiv0 (F : FormalGroup R) :
    MvPowerSeries.subst
        (![0, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R)
        (MvPowerSeries.pderiv 0 F.toSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.dX_at_zero := by
  classical
  have hsubst : MvPowerSeries.HasSubst
      (![0, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  have hX0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  ext e
  rw [MvPowerSeries.coeff_subst hsubst, PowerSeries.coeff_subst hX0]
  -- LHS: finsum over d : Fin 2 →₀ ℕ of coeff_d (pderiv 0 F) • coeff_e (vec^d)
  -- RHS: finsum over d : ℕ of coeff_d dX_at_zero • coeff_e (X 0)^d
  simp_rw [coeff_prod_subst_vec_zero_X0]
  -- LHS: finsum d, (if d 0 = 0 then coeff_d(pderiv 0 F) • coeff_e (X 0)^(d 1) else 0)
  simp_rw [smul_ite, smul_zero]
  -- Reindex the LHS along `n ↦ single 1 n` (the `d 0 = 0` slice), …
  rw [finsum_ite_first_eq_zero_eq_finsum_single_one]
  -- … then match the reindexed terms with the RHS coefficient-by-coefficient.
  exact finsum_congr fun n ↦ coeff_single_one_pderiv0_smul_eq_dX_at_zero F e n

/-! #### The `dX_at_zero` translation identity -/

/-- The diagonal substitution `![F.toSeries, F.toSeries]` has constant coefficient
zero in both slots, hence is a valid substitution. -/
private lemma hasSubst_diagF (F : FormalGroup R) :
    MvPowerSeries.HasSubst
      (![F.toSeries, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s; fin_cases s
  · exact FG.constantCoeff_FG_toSeries F
  · exact FG.constantCoeff_FG_toSeries F

/-- Composing the substitution `![F.toSeries, F.toSeries]` after `![0, X 0]` sends
slot `0` to `0` and slot `1` to `F.toSeries`, i.e. it equals `![0, F.toSeries]`. -/
private lemma subst_diagF_comp_shift0X0 (F : FormalGroup R) :
    (fun s ↦ MvPowerSeries.subst
      (![F.toSeries, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R)
      ((![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] :
        Fin 2 → MvPowerSeries (Fin 2) R) s)) =
      (![0, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R) := by
  have hb := hasSubst_diagF F
  funext s; fin_cases s
  · show MvPowerSeries.subst
      (![F.toSeries, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R) 0 = 0
    rw [← MvPowerSeries.substAlgHom_apply hb, map_zero]
  · show MvPowerSeries.subst
      (![F.toSeries, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R)
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = F.toSeries
    rw [MvPowerSeries.subst_X hb 0]; rfl

/-- Substituting `![F.toSeries, F.toSeries]` into `subst (X 0) F.dX_at_zero` collapses
the nested substitution to `subst F.toSeries F.dX_at_zero`. -/
private lemma subst_diagF_subst_X0_dX_at_zero (F : FormalGroup R) :
    MvPowerSeries.subst
      (![F.toSeries, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R)
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.dX_at_zero) =
      PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.dX_at_zero := by
  have hb := hasSubst_diagF F
  have hX0_unit : MvPowerSeries.HasSubst
      ((fun _ : Unit ↦ (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R))) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro _; simp
  show MvPowerSeries.subst _
    (MvPowerSeries.subst (fun _ : Unit ↦ (MvPowerSeries.X 0 :
        MvPowerSeries (Fin 2) R)) F.dX_at_zero) = _
  rw [MvPowerSeries.subst_comp_subst_apply hX0_unit hb]
  congr 1
  funext _
  rw [MvPowerSeries.subst_X hb 0]; rfl

/-- Auxiliary: `subst ![0, F.toSeries] (pderiv 0 F.toSeries) =
PowerSeries.subst F.toSeries F.dX_at_zero`. -/
private lemma subst_zero_F_pderiv0_eq (F : FormalGroup R) :
    MvPowerSeries.subst
        (![0, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R)
        (MvPowerSeries.pderiv 0 F.toSeries) =
      PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.dX_at_zero := by
  have hshift0X0 : MvPowerSeries.HasSubst
      (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s; fin_cases s <;> simp
  have happ := congr_arg (MvPowerSeries.subst
      (![F.toSeries, F.toSeries] : Fin 2 → MvPowerSeries (Fin 2) R))
    (subst_zero_X0_pderiv0 F)
  rw [MvPowerSeries.subst_comp_subst_apply hshift0X0 (hasSubst_diagF F),
      subst_diagF_comp_shift0X0 F, subst_diagF_subst_X0_dX_at_zero F] at happ
  exact happ

/-- **Silverman IV.4.2, intermediate step**: translation identity for
`F.dX_at_zero`.
`(dX_at_zero F)(T) · F_X(T, S) = (dX_at_zero F)(F(T, S))`
in `MvPowerSeries (Fin 2) R`. -/
theorem dX_at_zero_translation (F : FormalGroup R) :
    PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.dX_at_zero *
        MvPowerSeries.pderiv 0 F.toSeries =
      PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.dX_at_zero := by
  have key := congr_arg
    (MvPowerSeries.subst (shift3to2 R : Fin 3 → MvPowerSeries (Fin 2) R))
    (pderiv_assoc_identity F)
  rw [MvPowerSeries.subst_mul hasSubst_shift3to2,
      MvPowerSeries.subst_comp_subst_apply hasSubst_pairXY hasSubst_shift3to2,
      MvPowerSeries.subst_comp_subst_apply (hasSubst_assocL F) hasSubst_shift3to2,
      MvPowerSeries.subst_comp_subst_apply (hasSubst_assocR F) hasSubst_shift3to2,
      shift3to2_comp_pairXY, shift3to2_comp_assocL, shift3to2_comp_assocR] at key
  rw [subst_zero_X0_pderiv0] at key
  have hid : (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
      Fin 2 → MvPowerSeries (Fin 2) R) = MvPowerSeries.X := by
    funext s; fin_cases s <;> rfl
  rw [hid, congr_fun MvPowerSeries.subst_self (MvPowerSeries.pderiv 0 F.toSeries)] at key
  rw [subst_zero_F_pderiv0_eq] at key
  exact key

/-! #### The main theorem: translation invariance of the invariant differential -/

/-- **Silverman IV.4.2** — translation invariance of the invariant differential.

For a formal group `F/R`:
`ω_F(F(T, S)) · F_X(T, S) = ω_F(T)`
in `MvPowerSeries (Fin 2) R`, where `T = X 0`, `S = X 1`,
`F_X = pderiv 0 F.toSeries`, and `ω_F` is viewed as a bivariate series via
`PowerSeries.subst`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4, Prop. 4.2. -/
theorem invariantDiff_translation (F : FormalGroup R) :
    PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.invariantDiff *
        MvPowerSeries.pderiv 0 F.toSeries =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.invariantDiff := by
  have hX0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hF_subst : PowerSeries.HasSubst (F.toSeries : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (FG.constantCoeff_FG_toSeries F)
  set A : MvPowerSeries (Fin 2) R :=
    PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.dX_at_zero
  set B : MvPowerSeries (Fin 2) R := MvPowerSeries.pderiv 0 F.toSeries
  set C : MvPowerSeries (Fin 2) R :=
    PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.dX_at_zero
  set α : MvPowerSeries (Fin 2) R :=
    PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.invariantDiff
  set γ : MvPowerSeries (Fin 2) R :=
    PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.invariantDiff
  show γ * B = α
  have hAB : A * B = C := dX_at_zero_translation F
  have hAα : A * α = 1 := by
    show PowerSeries.subst _ F.dX_at_zero * PowerSeries.subst _ F.invariantDiff = 1
    rw [← PowerSeries.subst_mul hX0, F.dX_at_zero_mul_invariantDiff]
    rw [show PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) =
        (PowerSeries.substAlgHom hX0 :
          PowerSeries R →ₐ[R] MvPowerSeries (Fin 2) R)
        from (PowerSeries.coe_substAlgHom hX0).symm]
    exact (PowerSeries.substAlgHom hX0).map_one
  have hCγ : C * γ = 1 := by
    show PowerSeries.subst _ F.dX_at_zero * PowerSeries.subst _ F.invariantDiff = 1
    rw [← PowerSeries.subst_mul hF_subst, F.dX_at_zero_mul_invariantDiff]
    rw [show PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) =
        (PowerSeries.substAlgHom hF_subst :
          PowerSeries R →ₐ[R] MvPowerSeries (Fin 2) R)
        from (PowerSeries.coe_substAlgHom hF_subst).symm]
    exact (PowerSeries.substAlgHom hF_subst).map_one
  calc γ * B = B * γ := mul_comm _ _
    _ = 1 * (B * γ) := (one_mul _).symm
    _ = (α * A) * (B * γ) := by rw [mul_comm α A, hAα]
    _ = α * (A * B * γ) := by ring
    _ = α * (C * γ) := by rw [hAB]
    _ = α * 1 := by rw [hCγ]
    _ = α := mul_one _

end FormalGroup

end HasseWeil.FormalGroup

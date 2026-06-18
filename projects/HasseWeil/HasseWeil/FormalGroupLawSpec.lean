import HasseWeil.FormalGroup
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The specification layer for the legacy formal group law (Silverman IV §1)

This file is the *spec layer* for the coefficient-level formal-group-law
construction in `HasseWeil.FormalGroup` (Silverman, *The Arithmetic of
Elliptic Curves*, 2nd ed., IV §1, pp. 115–120). The legacy file constructs
`formalW`, `formalInverse` and `formalGroupLaw` by explicit coefficient
recursions; here we introduce the named bivariate series of Silverman's
chord construction (the slope `λ`, the intercept `ν`, the chord-cubic
coefficients `A` and `B`, the third root `z₃`) as honest `MvPowerSeries`
and prove the identities that characterise them:

* `formalSlopeBiv` (λ) with its divided-difference spec
  `formalSlopeBiv_spec : (X 1 - X 0) * λ = w∘X 1 - w∘X 0` and its diagonal
  `formalSlopeBiv_diag : λ∘(f,f) = w′∘f`;
* `weierstrassZWAt`, the `(z,w)`-chart Weierstrass operator
  `f(z₀, s) = z₀³ + a₁z₀s + a₂z₀²s + a₃s² + a₄z₀s² + a₆s³`, with the
  fixed-point repackaging `formalW_fixedPoint` of `formalW_recurrence`,
  the Hensel-style uniqueness `weierstrassZWAt_unique` (Silverman
  IV.1.1(b)/IV.1.2), and its substitution instance
  `subst_formalW_fixedPoint`;
* `formalNuBiv` (ν), `chordA`, `chordB`, `formalZ3` with the
  line-evaluation specs `line_eval_left`/`line_eval_right` and the
  constant-coefficient facts needed downstream.

## ⚠ Print errors in the source

The 2nd edition's displays for the line equation, `z₃` and the quartic
band of `F` on pp. 119–120 contain verified sign errors; the corrected
formulas (which `chordB`/`formalZ3` below and the legacy hardcoded band
follow) are recorded in `.mathlib-quality/plan-iv1.md` §References. Do
NOT "fix" this file to match the book.

## Implementation notes

* Everything is stated over an arbitrary `CommRing R`, the context of the
  host file `HasseWeil.FormalGroup`.
* The `ring`/`abel` tactics currently fail on `PowerSeries R` goals in
  this toolchain (instance-synthesis gap, see the note at the bottom of
  `HasseWeil.FormalGroup`); polynomial identities of power series are
  therefore proved abstractly over a generic commutative ring and
  instantiated. On `MvPowerSeries (Fin 2) R` both `ring` and
  `linear_combination` work and are used directly.
* `2 •`/`3 •` in `chordB` are ℕ-scalar actions (char-safe).
-/

open WeierstrassCurve PowerSeries Finset

namespace HasseWeil

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Coefficient API for `formalW` as a power series -/

/-- The coefficients of `formalW` are `formalW_coeff`. -/
@[simp]
theorem coeff_formalW (n : ℕ) : PowerSeries.coeff n (formalW W) = formalW_coeff W n :=
  PowerSeries.coeff_mk n _

/-- `w(z)` has zero constant term. -/
@[simp]
theorem constantCoeff_formalW : PowerSeries.constantCoeff (formalW W) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalW]
  exact formalW_coeff_zero W

/-- `w(z) = z³ + ⋯` has order at least 3. -/
theorem three_le_order_formalW : 3 ≤ (formalW W).order := by
  have h : ∀ i < 3, PowerSeries.coeff i (formalW W) = 0 := by
    intro i hi
    rw [coeff_formalW]
    interval_cases i
    · exact formalW_coeff_zero W
    · exact formalW_coeff_one W
    · exact formalW_coeff_two W
  exact_mod_cast PowerSeries.nat_le_order (formalW W) 3 h

/-- `formalW W` may be substituted into power series (its constant term vanishes). -/
theorem hasSubst_formalW : PowerSeries.HasSubst (formalW W) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_formalW W)

/-! ### Generic substitution helpers

Substituting the multivariate variable `X s` into a univariate power series
embeds it into the variable `s`; the coefficients are supported on the pure
`s`-rows. These small helpers are the workhorse for the divided-difference
spec below.
-/

/-- Coefficients of a univariate series substituted into the variable `X s`:
only multi-indices supported at `s` alone survive. -/
theorem coeff_subst_X {σ : Type*} [DecidableEq σ] (s : σ) (f : PowerSeries R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.subst (MvPowerSeries.X s) f) =
      if d = Finsupp.single s (d s) then PowerSeries.coeff (d s) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X s)]
  rw [finsum_eq_single _ (d s) fun n hn ↦ ?_]
  · rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial]
    split_ifs with h
    · rw [smul_eq_mul, mul_one]
    · rw [smul_zero]
  · rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg fun h ↦ hn ?_, smul_zero]
    rw [h, Finsupp.single_eq_same]

/-- The constant coefficient of `f∘(X s)` is the constant coefficient of `f`. -/
theorem constantCoeff_subst_X {σ : Type*} (s : σ) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X s) f) =
      PowerSeries.constantCoeff f := by
  classical
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_X, if_pos (by simp)]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

/-- Substitution fixes constants. -/
theorem subst_C {τ : Type*} (a : MvPowerSeries τ R) (ha : PowerSeries.HasSubst a) (r : R) :
    PowerSeries.subst a (PowerSeries.C r) = MvPowerSeries.C r := by
  conv_lhs => rw [← Polynomial.coe_C]
  rw [PowerSeries.subst_coe ha, Polynomial.aeval_C]
  rfl

/-- Substitution fixes constants (univariate-target version). -/
theorem subst_C' (a : PowerSeries R) (ha : PowerSeries.HasSubst a) (r : R) :
    PowerSeries.subst a (PowerSeries.C r) = PowerSeries.C r :=
  subst_C a ha r

/-- Coefficient of `X s * φ`: an index shift at `s`. -/
theorem coeff_X_mul {σ : Type*} (s : σ) (φ : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (MvPowerSeries.X s * φ) =
      if Finsupp.single s 1 ≤ d then MvPowerSeries.coeff (d - Finsupp.single s 1) φ else 0 := by
  rw [show (MvPowerSeries.X s : MvPowerSeries σ R)
        = MvPowerSeries.monomial (Finsupp.single s 1) (1 : R) from rfl,
    MvPowerSeries.coeff_monomial_mul]
  split_ifs <;> simp

/-! ### `Fin 2 →₀ ℕ` bookkeeping -/

private lemma fin2_finsupp_decomp (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext t
  fin_cases t <;> simp

private lemma fin2_eq_single_zero_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) ↔ d 1 = 0 := by
  constructor
  · intro h
    conv_lhs => rw [h]
    simp
  · intro h
    ext t
    fin_cases t <;> simp [h]

private lemma fin2_eq_single_one_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 1 (d 1) ↔ d 0 = 0 := by
  constructor
  · intro h
    conv_lhs => rw [h]
    simp
  · intro h
    ext t
    fin_cases t <;> simp [h]

/-! ### FG-A1: the bivariate slope series λ -/

/-- The bivariate slope series `λ(z₁,z₂) = (w(z₂) − w(z₁))/(z₂ − z₁)`, defined by
polynomial divided differences: `coeff (a,b) λ = formalW_coeff W (a + b + 1)`
(this is `(z₂ⁿ − z₁ⁿ)/(z₂ − z₁) = Σ_{i+j=n−1} z₁ⁱz₂ʲ` applied to each monomial
of `w`). Source: [Sil] IV §1, p. 119. -/
noncomputable def formalSlopeBiv (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  fun d ↦ formalW_coeff W (d 0 + d 1 + 1)

@[simp]
theorem coeff_formalSlopeBiv (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalSlopeBiv W) = formalW_coeff W (d 0 + d 1 + 1) :=
  rfl

/-- The divided-difference specification of the slope:
`(z₂ − z₁)·λ(z₁,z₂) = w(z₂) − w(z₁)` as bivariate power series. -/
theorem formalSlopeBiv_spec :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * formalSlopeBiv W
      = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (formalW W)
        - PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalW W) := by
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [sub_mul, map_sub, map_sub, coeff_X_mul, coeff_X_mul, coeff_subst_X, coeff_subst_X]
  simp only [fin2_eq_single_zero_iff, fin2_eq_single_one_iff, Finsupp.single_le_iff,
    coeff_formalSlopeBiv, coeff_formalW, Finsupp.tsub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), Nat.sub_zero]
  by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
  · rw [if_neg (by omega), if_neg (by omega), if_pos h0, if_pos h1, h0, h1, sub_self, sub_self]
  · rw [if_pos (by omega), if_neg (by omega), if_pos h0, if_neg h1, h0,
      show 0 + (d 1 - 1) + 1 = d 1 by omega]
  · rw [if_neg (by omega), if_pos (by omega), if_neg h0, if_pos h1, h1,
      show d 0 - 1 + 0 + 1 = d 0 by omega]
  · rw [if_pos (by omega), if_pos (by omega), if_neg h0, if_neg h1,
      show d 0 + (d 1 - 1) + 1 = d 0 + d 1 by omega,
      show d 0 - 1 + d 1 + 1 = d 0 + d 1 by omega, sub_self, sub_self]

/-- The slope series has zero constant coefficient (since `w` starts at `z³`). -/
@[simp]
theorem constantCoeff_formalSlopeBiv :
    MvPowerSeries.constantCoeff (formalSlopeBiv W) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalSlopeBiv]
  simpa using formalW_coeff_one W

/-- The linear coefficients of the slope series vanish (since `w` starts at `z³`). -/
@[simp]
theorem coeff_single_one_formalSlopeBiv (s : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single s 1) (formalSlopeBiv W) = 0 := by
  rw [coeff_formalSlopeBiv]
  fin_cases s <;> simpa using formalW_coeff_two W

/-- One term of the diagonal substitution: only multi-indices of total degree `n`
contribute, each with the same value `formalW_coeff W (n+1)`. -/
private lemma formalSlopeBiv_diag_term (n : ℕ) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalSlopeBiv W) •
        MvPowerSeries.coeff (Finsupp.single () n)
          (d.prod fun _ e ↦ (PowerSeries.X : PowerSeries R) ^ e)
      = if n = d 0 + d 1 then formalW_coeff W (n + 1) else 0 := by
  have hprod : (d.prod fun _ e ↦ (PowerSeries.X : PowerSeries R) ^ e)
      = (PowerSeries.X : PowerSeries R) ^ (d 0 + d 1) := by
    rw [Finsupp.prod_fintype d (fun _ e ↦ (PowerSeries.X : PowerSeries R) ^ e)
        (fun _ ↦ pow_zero _), Fin.prod_univ_two]
    exact (pow_add (PowerSeries.X : PowerSeries R) (d 0) (d 1)).symm
  rw [hprod,
    show MvPowerSeries.coeff (Finsupp.single () n)
        ((PowerSeries.X : PowerSeries R) ^ (d 0 + d 1))
      = PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ (d 0 + d 1)) from rfl,
    PowerSeries.coeff_X_pow, coeff_formalSlopeBiv]
  split_ifs with h
  · rw [smul_eq_mul, mul_one, h]
  · rw [smul_zero]

/-- The diagonal of the slope series at the variable (constant-family form):
`λ(z,z) = w′(z)`. -/
private theorem formalSlopeBiv_diag_const :
    MvPowerSeries.subst (fun _ : Fin 2 ↦ (PowerSeries.X : PowerSeries R)) (formalSlopeBiv W)
      = d⁄dX R (formalW W) := by
  have hX : MvPowerSeries.HasSubst (fun _ : Fin 2 ↦ (PowerSeries.X : PowerSeries R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ MvPowerSeries.constantCoeff_X ()
  apply PowerSeries.ext fun n ↦ ?_
  rw [show PowerSeries.coeff n
        (MvPowerSeries.subst (fun _ : Fin 2 ↦ (PowerSeries.X : PowerSeries R))
          (formalSlopeBiv W))
      = MvPowerSeries.coeff (Finsupp.single () n)
          (MvPowerSeries.subst (fun _ : Fin 2 ↦ (PowerSeries.X : PowerSeries R))
            (formalSlopeBiv W)) from rfl,
    MvPowerSeries.coeff_subst hX]
  refine (finsum_congr fun d ↦ formalSlopeBiv_diag_term W n d).trans ?_
  have hsupp : (Function.support fun d : Fin 2 →₀ ℕ ↦
        if n = d 0 + d 1 then formalW_coeff W (n + 1) else 0)
      ⊆ ↑((Finset.antidiagonal n).image fun p : ℕ × ℕ ↦
        Finsupp.single (0 : Fin 2) p.1 + Finsupp.single (1 : Fin 2) p.2) := by
    intro d hd
    have h : n = d 0 + d 1 := by
      by_contra hcon
      exact hd (if_neg hcon)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(d 0, d 1), Finset.mem_antidiagonal.mpr h.symm, (fin2_finsupp_decomp d).symm⟩)
  have hinj : Set.InjOn
      (fun p : ℕ × ℕ ↦ Finsupp.single (0 : Fin 2) p.1 + Finsupp.single (1 : Fin 2) p.2)
      ↑(Finset.antidiagonal n) := by
    intro p _ q _ hpq
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) hpq
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) hpq
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero, zero_add] at h0 h1
    exact Prod.ext h0 h1
  have hterm : ∀ p ∈ Finset.antidiagonal n,
      (if n = (Finsupp.single (0 : Fin 2) p.1 + Finsupp.single (1 : Fin 2) p.2) 0
            + (Finsupp.single (0 : Fin 2) p.1 + Finsupp.single (1 : Fin 2) p.2) 1
        then formalW_coeff W (n + 1) else 0) = formalW_coeff W (n + 1) := by
    intro p hp
    rw [if_pos]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero, zero_add]
    exact (Finset.mem_antidiagonal.mp hp).symm
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj,
    Finset.sum_congr rfl hterm, Finset.sum_const, Finset.Nat.card_antidiagonal,
    PowerSeries.coeff_derivative, coeff_formalW, nsmul_eq_mul, Nat.cast_add_one, mul_comm]

/-- The diagonal of the slope series at the variable: `λ(z,z) = w′(z)`. -/
theorem formalSlopeBiv_diag_X :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries R)
        (formalSlopeBiv W)
      = d⁄dX R (formalW W) := by
  rw [show (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries R)
      = fun _ : Fin 2 ↦ PowerSeries.X from funext fun s ↦ by fin_cases s <;> rfl]
  exact formalSlopeBiv_diag_const W

/-- **The diagonal of the slope series** (Silverman's `λ(z,z) = w′(z)`): substituting
the same series `f` (of positive order) into both slots of `λ` computes `w′∘f`. -/
theorem formalSlopeBiv_diag (f : PowerSeries R) (hf : 1 ≤ f.order) :
    MvPowerSeries.subst (![f, f] : Fin 2 → PowerSeries R) (formalSlopeBiv W)
      = PowerSeries.subst f (d⁄dX R (formalW W)) := by
  have hf0 : PowerSeries.constantCoeff f = 0 :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hf
  have hX : MvPowerSeries.HasSubst (fun _ : Fin 2 ↦ (PowerSeries.X : PowerSeries R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ MvPowerSeries.constantCoeff_X ()
  have hb : MvPowerSeries.HasSubst (fun _ : Unit ↦ f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ hf0
  rw [show (![f, f] : Fin 2 → PowerSeries R) = fun _ : Fin 2 ↦ f from
      funext fun s ↦ by fin_cases s <;> rfl,
    ← formalSlopeBiv_diag_const (R := R) W, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply hX hb]
  congr 1
  funext s
  exact (MvPowerSeries.subst_X (R := R) hb ()).symm

/-! ### FG-A2: the `(z,w)`-Weierstrass operator, its fixed point and uniqueness -/

/-- The `(z,w)`-chart Weierstrass equation as an operator on power series,
parametric in the substituted variable `z₀`:
`f(z₀, s) = z₀³ + a₁z₀s + a₂z₀²s + a₃s² + a₄z₀s² + a₆s³`.
Source: [Sil] IV §1, p. 116 (the recursion (IV.1.1) `w = f(z,w)`). -/
noncomputable def weierstrassZWAt (W : WeierstrassCurve R) (z₀ s : PowerSeries R) :
    PowerSeries R :=
  z₀ ^ 3 + PowerSeries.C W.a₁ * z₀ * s + PowerSeries.C W.a₂ * z₀ ^ 2 * s
    + PowerSeries.C W.a₃ * s ^ 2 + PowerSeries.C W.a₄ * z₀ * s ^ 2
    + PowerSeries.C W.a₆ * s ^ 3

/-- `formalW W` is a fixed point of the Weierstrass operator at `z₀ = X`:
this is `formalW_recurrence` repackaged. -/
theorem formalW_fixedPoint : formalW W = weierstrassZWAt W PowerSeries.X (formalW W) :=
  formalW_recurrence W

/-- The difference of two values of the Weierstrass operator factors through the
difference of the `s`-arguments; abstract commutative-ring identity (stated over a
generic ring because `ring` cannot currently normalise `PowerSeries R` goals). -/
private lemma weierstrassZW_sub_factor {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ z s s' : A) :
    (z ^ 3 + a₁ * z * s + a₂ * z ^ 2 * s + a₃ * s ^ 2 + a₄ * z * s ^ 2 + a₆ * s ^ 3)
      - (z ^ 3 + a₁ * z * s' + a₂ * z ^ 2 * s' + a₃ * s' ^ 2 + a₄ * z * s' ^ 2 + a₆ * s' ^ 3)
    = (s - s') * (a₁ * z + a₂ * z ^ 2 + a₃ * (s + s') + a₄ * z * (s + s')
        + a₆ * (s ^ 2 + s * s' + s' ^ 2)) := by
  ring

/-- **Hensel-style uniqueness for the `(z,w)`-Weierstrass recursion**
(Silverman IV.1.1(b)/IV.1.2, parametric in `z₀` per FG-B1's design note):
two power-series solutions of `s = f(z₀, s)` of positive order coincide.

The proof is the order bootstrap: the difference `d = s − s'` satisfies
`d = d·g` with `g` of positive order, forcing `d = 0`. -/
theorem weierstrassZWAt_unique (z₀ : PowerSeries R) (hz : 1 ≤ z₀.order)
    (s s' : PowerSeries R) (hs : 1 ≤ s.order) (hs' : 1 ≤ s'.order)
    (heq : s = weierstrassZWAt W z₀ s) (heq' : s' = weierstrassZWAt W z₀ s') : s = s' := by
  have hz0 : PowerSeries.constantCoeff z₀ = 0 :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hz
  have hs0 : PowerSeries.constantCoeff s = 0 :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hs
  have hs'0 : PowerSeries.constantCoeff s' = 0 :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hs'
  have key : s - s'
      = (s - s') * (PowerSeries.C W.a₁ * z₀ + PowerSeries.C W.a₂ * z₀ ^ 2
          + PowerSeries.C W.a₃ * (s + s') + PowerSeries.C W.a₄ * z₀ * (s + s')
          + PowerSeries.C W.a₆ * (s ^ 2 + s * s' + s' ^ 2)) := by
    conv_lhs => rw [heq, heq']
    exact weierstrassZW_sub_factor (PowerSeries.C W.a₁) (PowerSeries.C W.a₂)
      (PowerSeries.C W.a₃) (PowerSeries.C W.a₄) (PowerSeries.C W.a₆) z₀ s s'
  have hg : PowerSeries.constantCoeff
      (PowerSeries.C W.a₁ * z₀ + PowerSeries.C W.a₂ * z₀ ^ 2
        + PowerSeries.C W.a₃ * (s + s') + PowerSeries.C W.a₄ * z₀ * (s + s')
        + PowerSeries.C W.a₆ * (s ^ 2 + s * s' + s' ^ 2)) = 0 := by
    simp [hz0, hs0, hs'0]
  exact sub_eq_zero.mp (PowerSeries.eq_zero_of_self_eq_self_mul hg key)

/-- Substituting any `z₀` of positive order into `formalW`'s fixed-point equation:
`w∘z₀ = f(z₀, w∘z₀)`. This is the substitution principle feeding FG-B1. -/
theorem subst_formalW_fixedPoint (z₀ : PowerSeries R) (hz : 1 ≤ z₀.order) :
    PowerSeries.subst z₀ (formalW W)
      = weierstrassZWAt W z₀ (PowerSeries.subst z₀ (formalW W)) := by
  have hsub : PowerSeries.HasSubst z₀ :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hz)
  conv_lhs => rw [formalW_fixedPoint W]
  simp only [weierstrassZWAt, PowerSeries.subst_add hsub, PowerSeries.subst_mul hsub,
    PowerSeries.subst_pow hsub, PowerSeries.subst_X hsub, subst_C' z₀ hsub]

/-- The substitution `w∘z₀` has zero constant coefficient whenever `z₀` does. -/
theorem constantCoeff_subst_formalW (z₀ : PowerSeries R)
    (hz : PowerSeries.constantCoeff z₀ = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst z₀ (formalW W)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hz _ (constantCoeff_formalW W)

/-- The substitution `w∘z₀` has positive order whenever `z₀` does. -/
theorem one_le_order_subst_formalW (z₀ : PowerSeries R) (hz : 1 ≤ z₀.order) :
    1 ≤ PowerSeries.order (PowerSeries.subst z₀ (formalW W)) := by
  rw [PowerSeries.one_le_order_iff_constCoeff_eq_zero]
  exact constantCoeff_subst_formalW W z₀
    (PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp hz)

/-- Uniqueness against the canonical solution: any positive-order fixed point of
the Weierstrass operator at `z₀` *is* `w∘z₀`. This is the exact engine for FG-B1. -/
theorem eq_subst_formalW_of_fixedPoint (z₀ : PowerSeries R) (hz : 1 ≤ z₀.order)
    (s : PowerSeries R) (hs : 1 ≤ s.order) (heq : s = weierstrassZWAt W z₀ s) :
    s = PowerSeries.subst z₀ (formalW W) :=
  weierstrassZWAt_unique W z₀ hz s _ hs (one_le_order_subst_formalW W z₀ hz) heq
    (subst_formalW_fixedPoint W z₀ hz)

/-! ### FG-A3: ν, the chord-cubic coefficients A and B, and z₃ -/

/-- The intercept series `ν(z₁,z₂) = w(z₁) − z₁·λ(z₁,z₂)` of the chord through
the two formal points (the line is `w = λz + ν`; note the *corrected* sign, the
2nd-ed print has `w = λz − ν` — see the module docstring).
Source: [Sil] IV §1, p. 119. -/
noncomputable def formalNuBiv (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalW W)
    - MvPowerSeries.X 0 * formalSlopeBiv W

/-- ν has zero constant coefficient. -/
@[simp]
theorem constantCoeff_formalNuBiv : MvPowerSeries.constantCoeff (formalNuBiv W) = 0 := by
  rw [formalNuBiv, map_sub, map_mul, constantCoeff_subst_X, constantCoeff_formalW,
    constantCoeff_formalSlopeBiv, mul_zero, sub_zero]

/-- The first formal point lies on the line: `λ·z₁ + ν = w(z₁)` (definitional). -/
theorem line_eval_left :
    formalSlopeBiv W * MvPowerSeries.X 0 + formalNuBiv W
      = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalW W) := by
  rw [formalNuBiv, mul_comm (formalSlopeBiv W) (MvPowerSeries.X 0), add_sub_cancel]

/-- The second formal point lies on the line: `λ·z₂ + ν = w(z₂)`, by the
divided-difference spec (division-free). -/
theorem line_eval_right :
    formalSlopeBiv W * MvPowerSeries.X 1 + formalNuBiv W
      = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (formalW W) := by
  rw [formalNuBiv]
  linear_combination formalSlopeBiv_spec W

/-- `A = 1 + a₂λ + a₄λ² + a₆λ³` — the leading coefficient of the chord cubic
obtained by substituting `w = λz + ν` into the `(z,w)`-Weierstrass equation.
Source: [Sil] IV §1, p. 119. -/
noncomputable def chordA (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  1 + MvPowerSeries.C W.a₂ * formalSlopeBiv W + MvPowerSeries.C W.a₄ * formalSlopeBiv W ^ 2
    + MvPowerSeries.C W.a₆ * formalSlopeBiv W ^ 3

/-- `B = a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν` — the `z²`-coefficient of the chord
cubic. ⚠ This is the *corrected* form; the 2nd-ed print (p. 119) has wrong signs
in the `z₃` display — see `.mathlib-quality/plan-iv1.md` §References. Matches the
legacy `B` in `formalGroupLaw_coeff`. -/
noncomputable def chordB (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.C W.a₁ * formalSlopeBiv W + MvPowerSeries.C W.a₂ * formalNuBiv W
    + MvPowerSeries.C W.a₃ * formalSlopeBiv W ^ 2
    + 2 • (MvPowerSeries.C W.a₄ * formalSlopeBiv W * formalNuBiv W)
    + 3 • (MvPowerSeries.C W.a₆ * formalSlopeBiv W ^ 2 * formalNuBiv W)

/-- `A` has constant coefficient 1. -/
@[simp]
theorem constantCoeff_chordA : MvPowerSeries.constantCoeff (chordA W) = 1 := by
  simp [chordA]

/-- `A` is a unit (its constant coefficient is 1). -/
theorem isUnit_chordA : IsUnit (chordA W) :=
  MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_chordA]; exact isUnit_one)

/-- `A * A⁻¹ = 1` for the chosen unit inverse. -/
@[simp]
theorem chordA_mul_inv : chordA W * ↑(isUnit_chordA W).unit⁻¹ = 1 :=
  (isUnit_chordA W).mul_val_inv

/-- `A⁻¹ * A = 1` for the chosen unit inverse. -/
@[simp]
theorem chordA_inv_mul : (↑(isUnit_chordA W).unit⁻¹ : MvPowerSeries (Fin 2) R) * chordA W = 1 :=
  (isUnit_chordA W).val_inv_mul

/-- `B` has zero constant coefficient. -/
@[simp]
theorem constantCoeff_chordB : MvPowerSeries.constantCoeff (chordB W) = 0 := by
  simp [chordB]

/-- The third root of the chord cubic: `z₃ = −z₁ − z₂ − B·A⁻¹`. ⚠ Corrected form
(the 2nd-ed print of `z₃` on p. 119 has sign errors); matches the legacy `z3`
stream in `formalGroupLaw_coeff`. Source: [Sil] IV §1, pp. 119–120 with the
corrections of `.mathlib-quality/plan-iv1.md` §References. -/
noncomputable def formalZ3 (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  -MvPowerSeries.X 0 - MvPowerSeries.X 1 - chordB W * Units.val (isUnit_chordA W).unit⁻¹

/-- `z₃` has zero constant coefficient (so it can itself be substituted). -/
@[simp]
theorem constantCoeff_formalZ3 : MvPowerSeries.constantCoeff (formalZ3 W) = 0 := by
  simp [formalZ3]

/-! ### FG-A4: the `bmul`/`binv`/`bpow`/`bcomp` ↔ `MvPowerSeries` dictionary

The legacy `formalGroupLaw_coeff` computes, in degrees ≥ 5, with coefficient
streams `ℕ → ℕ → R` and the operations `bmul` (Cauchy product), `binv`
(unit inverse), `bpow` (powers) and `bcomp` (composition with a univariate
coefficient stream). `F_of` repackages a stream as an honest
`MvPowerSeries (Fin 2) R`; the dictionary lemmas identify each legacy
operation with the corresponding series operation.
-/

/-- Repackage a coefficient stream `ℕ → ℕ → R` as a bivariate power series. -/
def F_of (f : ℕ → ℕ → R) : MvPowerSeries (Fin 2) R :=
  fun d ↦ f (d 0) (d 1)

@[simp]
theorem coeff_F_of (f : ℕ → ℕ → R) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (F_of f) = f (d 0) (d 1) :=
  rfl

private lemma fin2_eq_zero_iff (d : Fin 2 →₀ ℕ) : d = 0 ↔ d 0 = 0 ∧ d 1 = 0 := by
  constructor
  · rintro rfl
    simp
  · intro h
    ext t
    fin_cases t <;> simp [h.1, h.2]

/-- The constant coefficient of a repackaged stream is its `(0,0)` entry. -/
theorem constantCoeff_F_of (f : ℕ → ℕ → R) :
    MvPowerSeries.constantCoeff (F_of f) = f 0 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_F_of]
  simp

/-- **The product dictionary**: the legacy Cauchy product `bmul` repackages to
the product of the repackaged series. -/
theorem F_of_bmul (f g : ℕ → ℕ → R) : F_of (bmul f g) = F_of f * F_of g := by
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [MvPowerSeries.coeff_mul, coeff_F_of]
  change (Finset.range (d 0 + 1)).sum (fun a ↦ (Finset.range (d 1 + 1)).sum fun b ↦
    f a b * g (d 0 - a) (d 1 - b)) = _
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (i := fun (x : ℕ × ℕ) _ ↦
      ((Finsupp.single (0 : Fin 2) x.1 + Finsupp.single (1 : Fin 2) x.2,
        Finsupp.single (0 : Fin 2) (d 0 - x.1) + Finsupp.single (1 : Fin 2) (d 1 - x.2)) :
        (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)))
    (j := fun p _ ↦ ((p.1 0, p.1 1) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hx
    rw [Finset.mem_antidiagonal]
    ext t
    fin_cases t <;>
      simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.isValue] <;>
      simp <;> omega
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have h0 : p.1 0 + p.2 0 = d 0 := by rw [← Finsupp.add_apply, hp]
    have h1 : p.1 1 + p.2 1 = d 1 := by rw [← Finsupp.add_apply, hp]
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
    omega
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hx
    simp [Finsupp.add_apply]
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have h0 : p.1 0 + p.2 0 = d 0 := by rw [← Finsupp.add_apply, hp]
    have h1 : p.1 1 + p.2 1 = d 1 := by rw [← Finsupp.add_apply, hp]
    refine Prod.ext ?_ ?_ <;> · ext t; fin_cases t <;>
      simp [Finsupp.add_apply] <;> omega
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hx
    simp [Finsupp.add_apply]

/-- Coefficients of a product of repackaged streams (ticket shape). -/
theorem coeff_F_of_mul (f g : ℕ → ℕ → R) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (F_of f * F_of g) = bmul f g (d 0) (d 1) := by
  rw [← F_of_bmul, coeff_F_of]

/-! #### The `binv` recursion -/

/-- Unfolding of the well-founded recursion underlying `binv_by_degree`. -/
theorem binv_by_degree_eq (f : ℕ → ℕ → R) (N : ℕ) :
    binv_by_degree f N = fun i j ↦
      if i + j ≠ N then 0
      else if i = 0 ∧ j = 0 then 1
      else -(Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦
        if a = i ∧ b = j then 0
        else (if a + b < N then binv f a b else 0) * f (i - a) (j - b) := by
  change WellFoundedRelation.wf.fix _ N = _
  rw [WellFoundedRelation.wf.fix_eq]
  rfl

@[simp]
theorem binv_zero_zero (f : ℕ → ℕ → R) : binv f 0 0 = 1 := by
  change binv_by_degree f (0 + 0) 0 0 = 1
  rw [binv_by_degree_eq]
  simp

/-- The defining recursion of the legacy bivariate inverse, with the
degree-truncation guard discharged. -/
theorem binv_eq_of_ne (f : ℕ → ℕ → R) (i j : ℕ) (hij : ¬(i = 0 ∧ j = 0)) :
    binv f i j = -(Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦
      if a = i ∧ b = j then 0 else binv f a b * f (i - a) (j - b) := by
  change binv_by_degree f (i + j) i j = _
  rw [binv_by_degree_eq]
  simp only [ne_eq, not_true_eq_false, if_false, if_neg hij]
  congr 1
  refine Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun b hb ↦ ?_
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_pos]
    simp only [Finset.mem_range, Nat.lt_succ_iff] at ha hb
    omega

/-- Extract the top-corner term from a rectangular double sum of `ite`s. -/
private lemma sum_rect_corner (h : ℕ → ℕ → R) (i j : ℕ) :
    ((Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦
      if a = i ∧ b = j then h a b else 0) = h i j := by
  have hrow : ∀ a, ((Finset.range (j + 1)).sum fun b ↦ if a = i ∧ b = j then h a b else 0)
      = if a = i then h a j else 0 := by
    intro a
    by_cases ha : a = i
    · subst ha
      rw [if_pos rfl]
      simp only [true_and]
      rw [Finset.sum_ite_eq' (Finset.range (j + 1)) j (h a),
        if_pos (Finset.self_mem_range_succ j)]
    · rw [if_neg ha]
      exact Finset.sum_eq_zero fun b _ ↦ if_neg fun hc ↦ ha hc.1
  rw [Finset.sum_congr rfl fun a _ ↦ hrow a,
    Finset.sum_ite_eq' (Finset.range (i + 1)) i (fun a ↦ h a j),
    if_pos (Finset.self_mem_range_succ i)]

/-- Split the top-corner term off a rectangular double sum. -/
private lemma sum_rect_split_corner (h : ℕ → ℕ → R) (i j : ℕ) :
    ((Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦ h a b)
      = h i j + (Finset.range (i + 1)).sum
          (fun a ↦ (Finset.range (j + 1)).sum fun b ↦ if a = i ∧ b = j then 0 else h a b) := by
  have hsplit : ∀ a b, h a b
      = (if a = i ∧ b = j then h a b else 0) + (if a = i ∧ b = j then 0 else h a b) := by
    intro a b
    split_ifs <;> simp
  calc ((Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦ h a b)
      = ((Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦
          (if a = i ∧ b = j then h a b else 0) + (if a = i ∧ b = j then 0 else h a b)) :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hsplit a b
    _ = ((Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦
          if a = i ∧ b = j then h a b else 0)
        + (Finset.range (i + 1)).sum (fun a ↦ (Finset.range (j + 1)).sum fun b ↦
          if a = i ∧ b = j then 0 else h a b) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_add_distrib
    _ = h i j + (Finset.range (i + 1)).sum (fun a ↦ (Finset.range (j + 1)).sum fun b ↦
          if a = i ∧ b = j then 0 else h a b) := by rw [sum_rect_corner]

/-- **The inverse dictionary**: for a stream with `f 0 0 = 1`, the legacy `binv`
repackages to a (left and hence two-sided) inverse of `F_of f`. -/
theorem F_of_binv_mul (f : ℕ → ℕ → R) (hf : f 0 0 = 1) :
    F_of (binv f) * F_of f = 1 := by
  rw [← F_of_bmul]
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [coeff_F_of, MvPowerSeries.coeff_one]
  change (Finset.range (d 0 + 1)).sum (fun a ↦ (Finset.range (d 1 + 1)).sum fun b ↦
    binv f a b * f (d 0 - a) (d 1 - b)) = _
  rw [sum_rect_split_corner, Nat.sub_self, Nat.sub_self, hf, mul_one]
  by_cases h : d = 0
  · rw [if_pos h]
    rw [fin2_eq_zero_iff] at h
    rw [h.1, h.2, binv_zero_zero]
    rw [show ((Finset.range (0 + 1)).sum fun a ↦ (Finset.range (0 + 1)).sum fun b ↦
        if a = 0 ∧ b = 0 then (0 : R) else binv f a b * f (0 - a) (0 - b)) = 0 by simp]
    exact add_zero 1
  · rw [if_neg h]
    rw [fin2_eq_zero_iff, not_and_or] at h
    rw [binv_eq_of_ne f (d 0) (d 1) (by tauto), neg_add_cancel]

/-! #### The `bpow` and `bcomp` dictionaries -/

theorem bpow_zero (f : ℕ → ℕ → R) (i j : ℕ) :
    bpow f i j 0 = if i = 0 ∧ j = 0 then 1 else 0 :=
  rfl

theorem bpow_succ (f : ℕ → ℕ → R) (i j n : ℕ) :
    bpow f i j (n + 1) = bmul f (fun a b ↦ bpow f a b n) i j :=
  rfl

theorem bpow_one (f : ℕ → ℕ → R) (i j : ℕ) : bpow f i j 1 = f i j := by
  have h : bpow f i j 1 = bmul f (fun a b ↦ bpow f a b 0) i j := bpow_succ f i j 0
  rw [h]
  change ((Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦
    f a b * bpow f (i - a) (j - b) 0) = f i j
  rw [← sum_rect_corner f i j]
  refine Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun b hb ↦ ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at ha hb
  rw [bpow_zero]
  by_cases hab : a = i ∧ b = j
  · rw [if_pos hab, if_pos (by omega : i - a = 0 ∧ j - b = 0), mul_one]
  · rw [if_neg hab, if_neg (by omega : ¬(i - a = 0 ∧ j - b = 0)), mul_zero]

/-- The legacy `bpow` repackages to powers of the repackaged series. -/
theorem F_of_bpow (s : ℕ → ℕ → R) (n : ℕ) :
    F_of s ^ n = F_of fun i j ↦ bpow s i j n := by
  induction n with
  | zero =>
      apply MvPowerSeries.ext fun d ↦ ?_
      rw [pow_zero, coeff_F_of, bpow_zero, MvPowerSeries.coeff_one]
      simp only [fin2_eq_zero_iff]
  | succ n ih =>
      rw [pow_succ', ih, ← F_of_bmul]
      exact congrArg F_of (funext fun i ↦ funext fun j ↦ (bpow_succ s i j n).symm)

/-- `bpow` vanishes above the total degree (for streams with zero constant term). -/
theorem bpow_eq_zero_of_lt (s : ℕ → ℕ → R) (hs : s 0 0 = 0) :
    ∀ n i j, i + j < n → bpow s i j n = 0 := by
  intro n
  induction n with
  | zero => exact fun i j h ↦ absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro i j h
      rw [bpow_succ]
      change ((Finset.range (i + 1)).sum fun a ↦ (Finset.range (j + 1)).sum fun b ↦
        s a b * bpow s (i - a) (j - b) n) = 0
      refine Finset.sum_eq_zero fun a ha ↦ Finset.sum_eq_zero fun b hb ↦ ?_
      simp only [Finset.mem_range, Nat.lt_succ_iff] at ha hb
      by_cases hab : a = 0 ∧ b = 0
      · rw [hab.1, hab.2, hs, zero_mul]
      · rw [ih (i - a) (j - b) (by omega), mul_zero]

/-- **The composition dictionary** (FG-A4): the legacy `bcomp` computes the
coefficients of `PowerSeries.subst` into the repackaged stream. -/
theorem coeff_subst_F_of (c : ℕ → R) (s : ℕ → ℕ → R) (hs : s 0 0 = 0) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.subst (F_of s) (PowerSeries.mk c))
      = bcomp c s (d 0) (d 1) := by
  have hsub : PowerSeries.HasSubst (F_of s) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [constantCoeff_F_of]; exact hs)
  rw [PowerSeries.coeff_subst hsub]
  rw [finsum_congr fun n ↦ by
    rw [PowerSeries.coeff_mk, F_of_bpow, coeff_F_of]]
  rw [finsum_eq_sum_of_support_subset _
    (s := Finset.range (d 0 + d 1 + 1)) ?_]
  · change (Finset.range (d 0 + d 1 + 1)).sum (fun n ↦ c n • bpow s (d 0) (d 1) n)
      = (Finset.range (d 0 + d 1 + 1)).sum fun n ↦ c n * bpow s (d 0) (d 1) n
    exact Finset.sum_congr rfl fun n _ ↦ smul_eq_mul ..
  · intro n hn
    by_contra hmem
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
    apply hn
    change c n • bpow s (d 0) (d 1) n = 0
    rw [bpow_eq_zero_of_lt s hs n _ _ (by omega), smul_zero]

/-! ### FG-A5: the inversion-series spec

The legacy `invDenom_coeff` recursion (FormalGroup.lean) computes the
inverse of `1 − a₁z − a₃w(z)`, and `formalInverse_coeff n = −invDenom (n−1)`
packages `i(z) = −z·(1 − a₁z − a₃w(z))⁻¹` — the expansion of Silverman's
`i(z) = x(z)/(y(z) + a₁x(z) + a₃)` through `x = z/w`, `y = −1/w`
([Sil] IV §1, p. 120). The closed form is verified here against the actual
recursion; no restatement (B2) was needed.
-/

/-- Unfolding of the well-founded recursion underlying `invDenom_coeff`. -/
theorem invDenom_coeff_eq (n : ℕ) :
    invDenom_coeff W n = if n = 0 then 1 else
      W.a₁ * (if n - 1 < n then invDenom_coeff W (n - 1) else 0)
        + (if n ≥ 3 then W.a₃ * (Finset.range (n - 2)).sum fun k ↦
            formalU_coeff W k * (if n - 3 - k < n then invDenom_coeff W (n - 3 - k) else 0)
          else 0) := by
  change WellFoundedRelation.wf.fix _ n = _
  rw [WellFoundedRelation.wf.fix_eq]
  rfl

@[simp]
theorem invDenom_coeff_zero : invDenom_coeff W 0 = 1 := by
  rw [invDenom_coeff_eq]
  simp

theorem invDenom_coeff_one : invDenom_coeff W 1 = W.a₁ := by
  rw [invDenom_coeff_eq]
  simp

theorem invDenom_coeff_two : invDenom_coeff W 2 = W.a₁ * W.a₁ := by
  rw [invDenom_coeff_eq]
  simp [invDenom_coeff_one]

theorem invDenom_coeff_three : invDenom_coeff W 3 = W.a₁ * (W.a₁ * W.a₁) + W.a₃ := by
  rw [invDenom_coeff_eq]
  simp [invDenom_coeff_two, formalU_coeff_zero]

/-- The defining recursion of `invDenom_coeff` at a successor index, with the
truncation guards discharged. -/
theorem invDenom_coeff_succ (n : ℕ) :
    invDenom_coeff W (n + 1) = W.a₁ * invDenom_coeff W n
      + (if 3 ≤ n + 1 then W.a₃ * (Finset.range (n - 1)).sum fun k ↦
          formalU_coeff W k * invDenom_coeff W (n - 2 - k)
        else 0) := by
  rw [invDenom_coeff_eq W (n + 1), if_neg (Nat.succ_ne_zero n)]
  congr 1
  · rw [show n + 1 - 1 = n from rfl, if_pos (Nat.lt_succ_self n)]
  · rw [show n + 1 - 2 = n - 1 from rfl]
    by_cases h3 : 3 ≤ n + 1
    · rw [if_pos h3, if_pos h3]
      congr 1
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [show n + 1 - 3 - k = n - 2 - k from rfl, if_pos (by omega)]
    · rw [if_neg h3, if_neg h3]

/-- Abstract rearrangement (stated over a generic commutative ring because
`ring` cannot currently normalise `PowerSeries R` goals). -/
private lemma mul_one_sub_sub {A : Type*} [CommRing A] (a u w a₁ a₃ : A) :
    a * (1 - a₁ * u - a₃ * w) = a - a₁ * (u * a) - a₃ * (w * a) := by
  ring

/-- The convolution of `formalW` against a coefficient stream, reindexed onto
the `formalU_coeff` tail (the first three `w`-coefficients vanish). -/
private lemma sum_formalW_mul_eq (g : ℕ → R) (n : ℕ) :
    ((Finset.range (n + 1 + 1)).sum fun i ↦ formalW_coeff W i * g (n + 1 - i))
      = if 3 ≤ n + 1 then
          (Finset.range (n - 1)).sum fun k ↦ formalU_coeff W k * g (n - 2 - k)
        else 0 := by
  by_cases h3 : 3 ≤ n + 1
  · rw [if_pos h3]
    conv_lhs => rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 3) (by omega : 3 ≤ n + 1 + 1)]
    rw [show ((Finset.Ico 0 3).sum fun i ↦ formalW_coeff W i * g (n + 1 - i)) = 0 from ?_,
      zero_add, Finset.sum_Ico_eq_sum_range]
    · refine Finset.sum_congr
        (congrArg Finset.range (show n + 1 + 1 - 3 = n - 1 by omega)) fun k _ ↦ ?_
      rw [show 3 + k = k + 3 from Nat.add_comm 3 k, show n + 1 - (k + 3) = n - 2 - k by omega]
      simp only [formalU_coeff]
    · rw [show Finset.Ico 0 3 = Finset.range 3 from by rw [Finset.range_eq_Ico],
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
        formalW_coeff_zero, formalW_coeff_one, formalW_coeff_two]
      simp
  · rw [if_neg h3]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    simp only [Finset.mem_range] at hi
    have hi3 : i < 3 := by omega
    interval_cases i <;>
      simp [formalW_coeff_zero, formalW_coeff_one, formalW_coeff_two]

/-- The legacy `invDenom` stream inverts `1 − a₁z − a₃w(z)`. -/
theorem invDenom_mul_eq_one :
    PowerSeries.mk (invDenom_coeff W)
      * (1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W) = 1 := by
  have h2 : PowerSeries.mk (invDenom_coeff W)
      - PowerSeries.C W.a₁ * (PowerSeries.X * PowerSeries.mk (invDenom_coeff W))
      - PowerSeries.C W.a₃ * (formalW W * PowerSeries.mk (invDenom_coeff W)) = 1 := by
    apply PowerSeries.ext fun n ↦ ?_
    rw [map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    cases n with
    | zero =>
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
    | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
          PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (M := R) (fun i j ↦ PowerSeries.coeff i (formalW W)
              * PowerSeries.coeff j (PowerSeries.mk (invDenom_coeff W))) (n + 1)]
        simp only [coeff_formalW, PowerSeries.coeff_mk]
        rw [sum_formalW_mul_eq W (invDenom_coeff W) n, invDenom_coeff_succ W n,
          PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
        by_cases h3 : 3 ≤ n + 1
        · rw [if_pos h3, if_pos h3]
          ring
        · rw [if_neg h3, if_neg h3]
          ring
  exact (mul_one_sub_sub (PowerSeries.mk (invDenom_coeff W)) PowerSeries.X
    (formalW W) (PowerSeries.C W.a₁) (PowerSeries.C W.a₃)).trans h2

@[simp]
theorem coeff_formalInverse (n : ℕ) :
    PowerSeries.coeff n (formalInverse W) = formalInverse_coeff W n :=
  PowerSeries.coeff_mk n _

/-- `formalInverse` is `−z·D(z)` for the inverse-denominator stream `D`. -/
theorem formalInverse_eq_neg_X_mul :
    formalInverse W = -(PowerSeries.X * PowerSeries.mk (invDenom_coeff W)) := by
  refine eq_neg_of_add_eq_zero_right (PowerSeries.ext fun n ↦ ?_)
  rw [map_add, coeff_formalInverse, map_zero]
  cases n with
  | zero =>
      simp [formalInverse_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
      simp [formalInverse_coeff]

/-- Abstract helper: `−(x·g)·f = −x` once `g·f = 1` (generic commutative ring;
`Neg`-headed rewrites do not fire on `PowerSeries R`). -/
private lemma neg_X_mul_helper {A : Type*} [CommRing A] (x g f : A) (h : g * f = 1) :
    -(x * g) * f = -x := by
  rw [neg_mul, mul_assoc, h, mul_one]

/-- **FG-A5, the inversion-series spec** ([Sil] IV §1 p. 120): the legacy
`formalInverse` recursion computes `i(z) = −z·(1 − a₁z − a₃w(z))⁻¹`; in
denominator-free form, `i(z)·(1 − a₁z − a₃w(z)) = −z`. The closed form
matches the recursion on the nose (no B2 restatement was needed). -/
theorem formalInverse_spec :
    formalInverse W * (1 - PowerSeries.C W.a₁ * PowerSeries.X
      - PowerSeries.C W.a₃ * formalW W) = -PowerSeries.X := by
  rw [formalInverse_eq_neg_X_mul]
  exact neg_X_mul_helper PowerSeries.X (PowerSeries.mk (invDenom_coeff W)) _
    (invDenom_mul_eq_one W)

/-- `i(z)` has zero constant term. -/
@[simp]
theorem constantCoeff_formalInverse :
    PowerSeries.constantCoeff (formalInverse W) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalInverse]
  simp [formalInverse_coeff]

/-- `i(z) = −z + ⋯`: the linear coefficient is `−1`. -/
theorem coeff_one_formalInverse : PowerSeries.coeff 1 (formalInverse W) = -1 := by
  rw [coeff_formalInverse]
  simp [formalInverse_coeff]

/-- `formalInverse W` may be substituted into power series. -/
theorem hasSubst_formalInverse : PowerSeries.HasSubst (formalInverse W) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_formalInverse W)

/-! ### The ingredient chain: legacy coefficient streams = the named series

`formalGroupLaw_coeff` computes, in its `bcomp` branch, with `let`-bound
streams `lam`/`w1`/`nu`/`A`/`B`/`z3`. We name these streams (definitionally
equal to the `let`-bound ones) and identify their `F_of` repackagings with
the FG-A1/A3 series `formalSlopeBiv`/`formalNuBiv`/`chordA`/`chordB`/
`formalZ3`.
-/

private noncomputable def lamS (W : WeierstrassCurve R) : ℕ → ℕ → R :=
  fun a b ↦ formalW_coeff W (a + b + 1)

private noncomputable def w1S (W : WeierstrassCurve R) : ℕ → ℕ → R :=
  fun a b ↦ if b = 0 then formalW_coeff W a else 0

private noncomputable def nuS (W : WeierstrassCurve R) : ℕ → ℕ → R :=
  fun a b ↦ w1S W a b - (if a ≥ 1 then lamS W (a - 1) b else 0)

private noncomputable def AS (W : WeierstrassCurve R) : ℕ → ℕ → R :=
  fun a b ↦ (if a = 0 ∧ b = 0 then 1 else 0) + W.a₂ * lamS W a b
    + W.a₄ * bmul (lamS W) (lamS W) a b
    + W.a₆ * bmul (lamS W) (bmul (lamS W) (lamS W)) a b

private noncomputable def BS (W : WeierstrassCurve R) : ℕ → ℕ → R :=
  fun a b ↦ W.a₁ * lamS W a b + W.a₂ * nuS W a b
    + W.a₃ * bmul (lamS W) (lamS W) a b
    + 2 * W.a₄ * bmul (lamS W) (nuS W) a b
    + 3 * W.a₆ * bmul (bmul (lamS W) (lamS W)) (nuS W) a b

private noncomputable def z3S (W : WeierstrassCurve R) : ℕ → ℕ → R :=
  fun a b ↦ -(bmul (BS W) (binv (AS W)) a b)
    - (if a = 1 ∧ b = 0 then 1 else 0) - (if a = 0 ∧ b = 1 then 1 else 0)

private lemma F_of_lamS : F_of (lamS W) = formalSlopeBiv W :=
  rfl

private lemma F_of_w1S :
    F_of (w1S W) = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalW W) := by
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [coeff_F_of, coeff_subst_X]
  simp only [w1S, coeff_formalW, fin2_eq_single_zero_iff]

private lemma F_of_nuS : F_of (nuS W) = formalNuBiv W := by
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [coeff_F_of, formalNuBiv, map_sub, ← F_of_w1S, coeff_F_of, coeff_X_mul,
    coeff_formalSlopeBiv]
  simp [nuS, lamS, Finsupp.single_le_iff, Finsupp.tsub_apply]

private lemma F_of_delta :
    F_of (fun a b ↦ if a = 0 ∧ b = 0 then (1 : R) else 0) = 1 := by
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [coeff_F_of, MvPowerSeries.coeff_one]
  simp only [fin2_eq_zero_iff]

private lemma fin2_eq_single01_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single (0 : Fin 2) 1 ↔ d 0 = 1 ∧ d 1 = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext t
    fin_cases t <;> simp [h0, h1]

private lemma fin2_eq_single11_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single (1 : Fin 2) 1 ↔ d 0 = 0 ∧ d 1 = 1 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext t
    fin_cases t <;> simp [h0, h1]

private lemma F_of_delta10 :
    F_of (fun a b ↦ if a = 1 ∧ b = 0 then (1 : R) else 0) = MvPowerSeries.X 0 := by
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [coeff_F_of, MvPowerSeries.coeff_X]
  simp only [fin2_eq_single01_iff]

private lemma F_of_delta01 :
    F_of (fun a b ↦ if a = 0 ∧ b = 1 then (1 : R) else 0) = MvPowerSeries.X 1 := by
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [coeff_F_of, MvPowerSeries.coeff_X]
  simp only [fin2_eq_single11_iff]

private lemma F_of_AS : F_of (AS W) = chordA W := by
  have hsum : F_of (AS W)
      = F_of (fun a b ↦ if a = 0 ∧ b = 0 then (1 : R) else 0)
        + MvPowerSeries.C W.a₂ * F_of (lamS W)
        + MvPowerSeries.C W.a₄ * F_of (bmul (lamS W) (lamS W))
        + MvPowerSeries.C W.a₆ * F_of (bmul (lamS W) (bmul (lamS W) (lamS W))) := by
    apply MvPowerSeries.ext fun d ↦ ?_
    rw [map_add, map_add, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_C_mul, coeff_F_of, coeff_F_of, coeff_F_of, coeff_F_of]
    rfl
  rw [hsum, F_of_delta]
  simp only [F_of_bmul, F_of_lamS]
  rw [chordA]
  ring

private lemma F_of_BS : F_of (BS W) = chordB W := by
  have hsum : F_of (BS W)
      = MvPowerSeries.C W.a₁ * F_of (lamS W) + MvPowerSeries.C W.a₂ * F_of (nuS W)
        + MvPowerSeries.C W.a₃ * F_of (bmul (lamS W) (lamS W))
        + MvPowerSeries.C (2 * W.a₄) * F_of (bmul (lamS W) (nuS W))
        + MvPowerSeries.C (3 * W.a₆) * F_of (bmul (bmul (lamS W) (lamS W)) (nuS W)) := by
    apply MvPowerSeries.ext fun d ↦ ?_
    rw [map_add, map_add, map_add, map_add, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_C_mul, coeff_F_of, coeff_F_of, coeff_F_of, coeff_F_of,
      coeff_F_of, coeff_F_of]
    rfl
  rw [hsum]
  simp only [F_of_bmul, F_of_lamS, F_of_nuS, map_mul, map_ofNat]
  rw [chordB]
  ring

private lemma F_of_binv_AS :
    F_of (binv (AS W)) = ↑(isUnit_chordA W).unit⁻¹ := by
  have h1 : F_of (binv (AS W)) * chordA W = 1 := by
    rw [← F_of_AS]
    exact F_of_binv_mul (AS W)
      (by simp [AS, lamS, bmul, formalW_coeff_one])
  exact left_inv_eq_right_inv h1 (chordA_mul_inv W)

private lemma F_of_z3S : F_of (z3S W) = formalZ3 W := by
  have hsum : F_of (z3S W)
      = -F_of (bmul (BS W) (binv (AS W)))
        - F_of (fun a b ↦ if a = 1 ∧ b = 0 then (1 : R) else 0)
        - F_of (fun a b ↦ if a = 0 ∧ b = 1 then (1 : R) else 0) := by
    apply MvPowerSeries.ext fun d ↦ ?_
    rw [map_sub, map_sub, map_neg, coeff_F_of, coeff_F_of, coeff_F_of, coeff_F_of]
    rfl
  rw [hsum, F_of_bmul, F_of_BS, F_of_binv_AS, F_of_delta10, F_of_delta01, formalZ3]
  ring

private lemma z3S_zero_zero : z3S W 0 0 = 0 := by
  simpa only [constantCoeff_F_of, constantCoeff_formalZ3]
    using congrArg MvPowerSeries.constantCoeff (F_of_z3S W)

/-- The coefficients of the legacy formal group law. -/
theorem coeff_formalGroupLaw (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroupLaw W).toMvPowerSeries = formalGroupLaw_coeff W d :=
  rfl

/-- In its generic branch (`i, j ≥ 1`, `i + j ∉ {2,3,4}`), the legacy group-law
coefficient is the `bcomp` composition against the `z3S` stream. -/
private lemma formalGroupLaw_coeff_tail (d : Fin 2 →₀ ℕ) (h0 : d 0 ≠ 0) (h1 : d 1 ≠ 0)
    (h2 : d 0 + d 1 ≠ 2) (h3 : d 0 + d 1 ≠ 3) (h4 : d 0 + d 1 ≠ 4) :
    formalGroupLaw_coeff W d = bcomp (formalInverse_coeff W) (z3S W) (d 0) (d 1) := by
  simp only [formalGroupLaw_coeff]
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  rfl

/-! ### The unit rows of the chord composition

The legacy law hardcodes its unit rows `F(0,z₂) = z₂` and `F(z₁,0) = z₁` on
the *entire* rows `i = 0` / `j = 0`; for the spec theorem we must prove the
chord composition `i ∘ z₃` satisfies them. Substituting `z₁ := 0` (resp.
`z₂ := 0`) collapses the chord construction onto the one-variable series
`λ₀(z) = w(z)/z`: the chord through `(0,0)` and `(z, w(z))` meets the cubic
in the third root `ζ = −z − B₀/A₀`, the quadratic relation
`λ₀ = A₀z² + B₀z` transports to `ζ` by Vieta (division-free), `w(ζ) = λ₀ζ`
follows from FG-A2's Hensel uniqueness, and `i(ζ) = z` is then ring algebra
against FG-A5. All `PowerSeries` polynomial identities are proven abstractly
over a commutative ring and instantiated (the `ring`-on-`PowerSeries` gap).
-/

/-- The substitution family killing all variables except `s` (sent to `X`). -/
private noncomputable def rowFamily (s : Fin 2) : Fin 2 → PowerSeries R :=
  fun i ↦ if i = s then PowerSeries.X else 0

private lemma hasSubst_rowFamily (s : Fin 2) :
    MvPowerSeries.HasSubst (rowFamily (R := R) s) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by
    by_cases h : i = s
    · rw [show rowFamily (R := R) s i = PowerSeries.X from if_pos h]
      exact PowerSeries.constantCoeff_X
    · rw [show rowFamily (R := R) s i = 0 from if_neg h]
      exact map_zero _

private lemma prod_rowFamily (s : Fin 2) (d : Fin 2 →₀ ℕ) :
    (d.prod fun i e ↦ (rowFamily (R := R) s i) ^ e)
      = if d = Finsupp.single s (d s) then (PowerSeries.X : PowerSeries R) ^ (d s) else 0 := by
  rw [Finsupp.prod_fintype d (fun i e ↦ (rowFamily (R := R) s i) ^ e) fun _ ↦ pow_zero _,
    Fin.prod_univ_two]
  fin_cases s
  · simp only [Fin.zero_eta, Fin.isValue]
    change (rowFamily (R := R) 0 0) ^ (d 0) * (rowFamily (R := R) 0 1) ^ (d 1) = _
    rw [show rowFamily (R := R) 0 0 = PowerSeries.X from rfl,
      show rowFamily (R := R) 0 1 = 0 from rfl]
    by_cases h1 : d 1 = 0
    · rw [h1, pow_zero, if_pos ((fin2_eq_single_zero_iff d).mpr h1)]
      exact mul_one _
    · rw [if_neg fun hc ↦ h1 ((fin2_eq_single_zero_iff d).mp hc)]
      exact (congrArg (fun t ↦ (PowerSeries.X : PowerSeries R) ^ (d 0) * t)
        (zero_pow h1)).trans (mul_zero _)
  · simp only [Fin.mk_one, Fin.isValue]
    change (rowFamily (R := R) 1 0) ^ (d 0) * (rowFamily (R := R) 1 1) ^ (d 1) = _
    rw [show rowFamily (R := R) 1 0 = 0 from rfl,
      show rowFamily (R := R) 1 1 = PowerSeries.X from rfl]
    by_cases h0 : d 0 = 0
    · rw [h0, pow_zero, if_pos ((fin2_eq_single_one_iff d).mpr h0)]
      exact one_mul _
    · rw [if_neg fun hc ↦ h0 ((fin2_eq_single_one_iff d).mp hc)]
      exact (congrArg (fun t ↦ t * (PowerSeries.X : PowerSeries R) ^ (d 1))
        (zero_pow h0)).trans (zero_mul _)

/-- One term of the row-extraction finsum. -/
private lemma coeff_subst_rowFamily_term (s : Fin 2) (n : ℕ) (φ : MvPowerSeries (Fin 2) R)
    (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d φ • MvPowerSeries.coeff (Finsupp.single () n)
        (d.prod fun i e ↦ (rowFamily (R := R) s i) ^ e)
      = if d = Finsupp.single s n then MvPowerSeries.coeff d φ else 0 := by
  rw [prod_rowFamily]
  by_cases hds : d = Finsupp.single s (d s)
  · rw [if_pos hds,
      show MvPowerSeries.coeff (Finsupp.single () n) ((PowerSeries.X : PowerSeries R) ^ (d s))
        = PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ (d s)) from rfl,
      PowerSeries.coeff_X_pow]
    by_cases hsn : d s = n
    · rw [if_pos hsn.symm, smul_eq_mul, mul_one, if_pos (by rw [hds, hsn])]
    · rw [if_neg fun h ↦ hsn h.symm, smul_zero,
        if_neg fun hc ↦ hsn (by rw [hc, Finsupp.single_eq_same])]
  · rw [if_neg hds, if_neg fun hc ↦ hds (by rw [hc, Finsupp.single_eq_same])]
    exact (congrArg (fun t ↦ MvPowerSeries.coeff d φ • t)
      ((MvPowerSeries.coeff (Finsupp.single () n)).map_zero)).trans (smul_zero _)

/-- Row extraction: the coefficients of a `rowFamily` substitution are the
row-`s` coefficients of the bivariate series. -/
private lemma coeff_subst_rowFamily (s : Fin 2) (φ : MvPowerSeries (Fin 2) R) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.subst (rowFamily (R := R) s) φ)
      = MvPowerSeries.coeff (Finsupp.single s n) φ := by
  rw [show PowerSeries.coeff n (MvPowerSeries.subst (rowFamily (R := R) s) φ)
      = MvPowerSeries.coeff (Finsupp.single () n)
          (MvPowerSeries.subst (rowFamily (R := R) s) φ) from rfl,
    MvPowerSeries.coeff_subst (hasSubst_rowFamily s)]
  refine (finsum_congr fun d ↦ coeff_subst_rowFamily_term s n φ d).trans ?_
  rw [finsum_eq_single _ (Finsupp.single s n) fun d hd ↦ if_neg hd, if_pos rfl]

/-- Substitution fixes constants (multivariate source, univariate target). -/
private lemma mv_subst_C (a : Fin 2 → PowerSeries R) (r : R) :
    MvPowerSeries.subst a (MvPowerSeries.C r) = PowerSeries.C r := by
  rw [show (MvPowerSeries.C r : MvPowerSeries (Fin 2) R)
      = ((MvPolynomial.C r : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) from
        (MvPolynomial.coe_C r).symm,
    MvPowerSeries.subst_coe, MvPolynomial.aeval_C]
  rfl

/-- The one-variable slope `λ₀(z) = w(z)/z = z² + ⋯` (the row specialization of
`formalSlopeBiv`). -/
private noncomputable def lam0 (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ formalW_coeff W (n + 1)

private lemma X_mul_lam0 : PowerSeries.X * lam0 W = formalW W := by
  apply PowerSeries.ext fun n ↦ ?_
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, formalW_coeff_zero]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, coeff_formalW]
      exact PowerSeries.coeff_mk n _

private lemma constantCoeff_lam0 : PowerSeries.constantCoeff (lam0 W) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact (PowerSeries.coeff_mk 0 _).trans (formalW_coeff_one W)

/-- `A₀ = A(λ₀)`, the row specialization of `chordA`. -/
private noncomputable def A0 (W : WeierstrassCurve R) : PowerSeries R :=
  1 + PowerSeries.C W.a₂ * lam0 W + PowerSeries.C W.a₄ * lam0 W ^ 2
    + PowerSeries.C W.a₆ * lam0 W ^ 3

/-- `B₀ = a₁λ₀ + a₃λ₀²`, the row specialization of `chordB` (the ν-terms die). -/
private noncomputable def B0 (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.C W.a₁ * lam0 W + PowerSeries.C W.a₃ * lam0 W ^ 2

/-- Abstract collapse of the `ν = 0` specialization of `chordB` (generic
commutative ring; `simp`/`ring` cannot normalise `PowerSeries R`). -/
private lemma chordB_collapse {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ l : A) :
    a₁ * l + a₂ * 0 + a₃ * l ^ 2 + 2 • (a₄ * l * 0) + 3 • (a₆ * l ^ 2 * 0)
      = a₁ * l + a₃ * l ^ 2 := by
  ring

/-- Abstract cubic factorization feeding the quadratic relation (generic
commutative ring; `ring` cannot normalise `PowerSeries R`). -/
private lemma cubic_factor_abstract {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ z l : A)
    (h : z * l = z ^ 3 + a₁ * z * (z * l) + a₂ * z ^ 2 * (z * l) + a₃ * (z * l) ^ 2
      + a₄ * z * (z * l) ^ 2 + a₆ * (z * l) ^ 3) :
    z * ((1 + a₂ * l + a₄ * l ^ 2 + a₆ * l ^ 3) * z ^ 2 + (a₁ * l + a₃ * l ^ 2) * z - l)
      = 0 := by
  linear_combination -h

private lemma X_mul_cancel {f : PowerSeries R} (h : PowerSeries.X * f = 0) : f = 0 := by
  apply PowerSeries.ext fun n ↦ ?_
  have h2 := congrArg (PowerSeries.coeff (n + 1)) h
  rw [PowerSeries.coeff_succ_X_mul, map_zero] at h2
  rw [h2, map_zero]

/-- **The quadratic relation** `λ₀ = A₀z² + B₀z`, from the `w`-recursion at
`w = z·λ₀` after cancelling the regular element `z`. -/
private lemma lam0_eq : lam0 W = A0 W * PowerSeries.X ^ 2 + B0 W * PowerSeries.X := by
  have h : PowerSeries.X * lam0 W
      = PowerSeries.X ^ 3
        + PowerSeries.C W.a₁ * PowerSeries.X * (PowerSeries.X * lam0 W)
        + PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * (PowerSeries.X * lam0 W)
        + PowerSeries.C W.a₃ * (PowerSeries.X * lam0 W) ^ 2
        + PowerSeries.C W.a₄ * PowerSeries.X * (PowerSeries.X * lam0 W) ^ 2
        + PowerSeries.C W.a₆ * (PowerSeries.X * lam0 W) ^ 3 := by
    rw [X_mul_lam0]
    exact formalW_recurrence W
  have h0 := X_mul_cancel (cubic_factor_abstract (PowerSeries.C W.a₁) (PowerSeries.C W.a₂)
    (PowerSeries.C W.a₃) (PowerSeries.C W.a₄) (PowerSeries.C W.a₆) PowerSeries.X (lam0 W) h)
  exact (sub_eq_zero.mp h0).symm

private lemma rowEval_formalSlopeBiv (s : Fin 2) :
    MvPowerSeries.subst (rowFamily (R := R) s) (formalSlopeBiv W) = lam0 W := by
  apply PowerSeries.ext fun n ↦ ?_
  rw [coeff_subst_rowFamily, coeff_formalSlopeBiv, lam0, PowerSeries.coeff_mk]
  congr 1
  fin_cases s <;> simp

private lemma nuS_row0 (a : ℕ) : nuS W a 0 = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [nuS, w1S, formalW_coeff_zero]
  · have h1 : a ≥ 1 := ha
    simp [nuS, w1S, lamS, h1, show a - 1 + 0 + 1 = a from by omega]

private lemma nuS_row1 (b : ℕ) : nuS W 0 b = 0 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [nuS, w1S, formalW_coeff_zero]
  · simp [nuS, w1S, hb.ne']

private lemma rowEval_formalNuBiv (s : Fin 2) :
    MvPowerSeries.subst (rowFamily (R := R) s) (formalNuBiv W) = 0 := by
  apply PowerSeries.ext fun n ↦ ?_
  rw [coeff_subst_rowFamily, ← F_of_nuS, coeff_F_of]
  refine Eq.trans ?_ ((PowerSeries.coeff n).map_zero).symm
  fin_cases s
  · simpa using nuS_row0 W n
  · simpa using nuS_row1 W n

private lemma rowSubst_one (s : Fin 2) :
    MvPowerSeries.subst (rowFamily (R := R) s) (1 : MvPowerSeries (Fin 2) R) = 1 := by
  rw [show (1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.C 1 from (map_one _).symm,
    mv_subst_C, map_one]

private lemma rowSubst_nsmul (s : Fin 2) (n : ℕ) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.subst (rowFamily (R := R) s) (n • f)
      = n • MvPowerSeries.subst (rowFamily (R := R) s) f := by
  have h := map_nsmul (MvPowerSeries.substAlgHom (R := R) (hasSubst_rowFamily (R := R) s)) n f
  rwa [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply] at h

private lemma rowSubst_sub (s : Fin 2) (f g : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.subst (rowFamily (R := R) s) (f - g)
      = MvPowerSeries.subst (rowFamily (R := R) s) f
        - MvPowerSeries.subst (rowFamily (R := R) s) g := by
  have h := map_sub (MvPowerSeries.substAlgHom (R := R) (hasSubst_rowFamily (R := R) s)) f g
  rwa [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.substAlgHom_apply] at h

private lemma rowSubst_neg (s : Fin 2) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.subst (rowFamily (R := R) s) (-f)
      = -MvPowerSeries.subst (rowFamily (R := R) s) f := by
  have h := map_neg (MvPowerSeries.substAlgHom (R := R) (hasSubst_rowFamily (R := R) s)) f
  rwa [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply] at h

private lemma rowEval_chordA (s : Fin 2) :
    MvPowerSeries.subst (rowFamily (R := R) s) (chordA W) = A0 W := by
  have hs := hasSubst_rowFamily (R := R) s
  simp only [chordA]
  rw [MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs,
    MvPowerSeries.subst_pow hs, MvPowerSeries.subst_pow hs, rowEval_formalSlopeBiv,
    mv_subst_C, mv_subst_C, mv_subst_C, rowSubst_one]
  rfl

private lemma rowEval_chordB (s : Fin 2) :
    MvPowerSeries.subst (rowFamily (R := R) s) (chordB W) = B0 W := by
  have hs := hasSubst_rowFamily (R := R) s
  simp only [chordB]
  rw [MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    MvPowerSeries.subst_add hs, rowSubst_nsmul, rowSubst_nsmul,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_pow hs,
    rowEval_formalSlopeBiv, rowEval_formalNuBiv, mv_subst_C, mv_subst_C, mv_subst_C,
    mv_subst_C, mv_subst_C]
  exact chordB_collapse _ _ _ _ _ _

private lemma row_z3_zero_case {A : Type*} [CommRing A] (x y : A) :
    -x - 0 - y = -x - y := by
  ring

private lemma row_z3_one_case {A : Type*} [CommRing A] (x y : A) :
    -(0 : A) - x - y = -x - y := by
  ring

private lemma rowEval_formalZ3 (s : Fin 2) :
    MvPowerSeries.subst (rowFamily (R := R) s) (formalZ3 W)
      = -PowerSeries.X - B0 W
          * MvPowerSeries.subst (rowFamily (R := R) s)
              (↑(isUnit_chordA W).unit⁻¹ : MvPowerSeries (Fin 2) R) := by
  have hs := hasSubst_rowFamily (R := R) s
  simp only [formalZ3]
  rw [rowSubst_sub, rowSubst_sub, rowSubst_neg, MvPowerSeries.subst_mul hs, rowEval_chordB,
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  fin_cases s
  · exact row_z3_zero_case _ _
  · exact row_z3_one_case _ _

/-- Abstract: the quadratic relation transports from the root `x` to the
conjugate root `−x − bv` (Vieta, division-free). -/
private lemma quad_at_third_root {A : Type*} [CommRing A] (a b l x v : A) (hv : a * v = 1)
    (hq : a * x ^ 2 + b * x - l = 0) :
    a * (-x - b * v) ^ 2 + b * (-x - b * v) - l = 0 := by
  linear_combination hq + (2 * b * x + b ^ 2 * v) * hv

/-- Abstract: a root of the quadratic gives a fixed point of the `(z,w)`
Weierstrass operator along the line `w = lz`. -/
private lemma fixedPoint_of_quad {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ l z : A)
    (hq : (1 + a₂ * l + a₄ * l ^ 2 + a₆ * l ^ 3) * z ^ 2 + (a₁ * l + a₃ * l ^ 2) * z - l
      = 0) :
    l * z = z ^ 3 + a₁ * z * (l * z) + a₂ * z ^ 2 * (l * z) + a₃ * (l * z) ^ 2
      + a₄ * z * (l * z) ^ 2 + a₆ * (l * z) ^ 3 := by
  linear_combination (-z) * hq

/-- Abstract: the FG-A5 denominator evaluated at the third root recovers `−ζ/X`. -/
private lemma star_identity {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ l x v : A)
    (hv : (1 + a₂ * l + a₄ * l ^ 2 + a₆ * l ^ 3) * v = 1)
    (hl : l = (1 + a₂ * l + a₄ * l ^ 2 + a₆ * l ^ 3) * x ^ 2
      + (a₁ * l + a₃ * l ^ 2) * x) :
    -(-x - (a₁ * l + a₃ * l ^ 2) * v)
      = x * (1 - a₁ * (-x - (a₁ * l + a₃ * l ^ 2) * v)
          - a₃ * (l * (-x - (a₁ * l + a₃ * l ^ 2) * v))) := by
  linear_combination ((a₁ + a₃ * l) * v) * hl + ((a₁ + a₃ * l) * x ^ 2) * hv

/-- Abstract assembly of the row identity. -/
private lemma row_final_abstract {A : Type*} [CommRing A] (i dζ ζ x u : A)
    (h5 : i + ζ * dζ = 0) (hstar : -ζ = x * u) (hDU : dζ * u = 1) : i = x := by
  linear_combination h5 + dζ * hstar + x * hDU

/-- **The unit-row identity**: substituting either row family into `z₃` and
composing with `i` gives back the surviving variable, `i(z₃)|_{zₛ′=0} = zₛ`. -/
private lemma subst_rowZ3_formalInverse (s : Fin 2) :
    PowerSeries.subst (MvPowerSeries.subst (rowFamily (R := R) s) (formalZ3 W))
      (formalInverse W) = PowerSeries.X := by
  have hs := hasSubst_rowFamily (R := R) s
  set v := MvPowerSeries.subst (rowFamily (R := R) s)
    (↑(isUnit_chordA W).unit⁻¹ : MvPowerSeries (Fin 2) R) with hvdef
  set ζ := MvPowerSeries.subst (rowFamily (R := R) s) (formalZ3 W) with hζdef
  have hζ_eq : ζ = -PowerSeries.X - B0 W * v := rowEval_formalZ3 W s
  have hv : A0 W * v = 1 := by
    rw [← rowEval_chordA W s, hvdef, ← MvPowerSeries.subst_mul hs, chordA_mul_inv,
      show (1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.C 1 from (map_one _).symm,
      mv_subst_C, map_one]
  have hζ0 : PowerSeries.constantCoeff ζ = 0 := by
    rw [hζdef, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_rowFamily,
      Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_formalZ3 W
  have hζsub : PowerSeries.HasSubst ζ :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hζ0
  have hζord : 1 ≤ PowerSeries.order ζ :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hζ0
  -- the quadratic relation at the third root
  have hq0 : A0 W * ζ ^ 2 + B0 W * ζ - lam0 W = 0 := by
    rw [hζ_eq]
    exact quad_at_third_root (A0 W) (B0 W) (lam0 W) PowerSeries.X v hv
      (sub_eq_zero.mpr (lam0_eq W).symm)
  -- w(ζ) = λ₀ζ by Hensel uniqueness
  have hfp : lam0 W * ζ = weierstrassZWAt W ζ (lam0 W * ζ) :=
    fixedPoint_of_quad (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃)
      (PowerSeries.C W.a₄) (PowerSeries.C W.a₆) (lam0 W) ζ hq0
  have hlζord : 1 ≤ PowerSeries.order (lam0 W * ζ) := by
    rw [PowerSeries.one_le_order_iff_constCoeff_eq_zero, map_mul, hζ0, mul_zero]
  have hWζ : PowerSeries.subst ζ (formalW W) = lam0 W * ζ :=
    (eq_subst_formalW_of_fixedPoint W ζ hζord (lam0 W * ζ) hlζord hfp).symm
  -- the FG-A5 spec substituted at ζ
  have h1subst : PowerSeries.subst (R := R) ζ (1 : PowerSeries R) = 1 := by
    rw [show (1 : PowerSeries R) = PowerSeries.C 1 from (map_one _).symm,
      subst_C' ζ hζsub, map_one]
  have hsubsub : ∀ f g : PowerSeries R, PowerSeries.subst ζ (f - g)
      = PowerSeries.subst ζ f - PowerSeries.subst ζ g := fun f g ↦ by
    have h := map_sub (PowerSeries.substAlgHom (R := R) hζsub) f g
    rwa [PowerSeries.coe_substAlgHom hζsub] at h
  have hT : PowerSeries.subst ζ (1 - PowerSeries.C W.a₁ * PowerSeries.X
        - PowerSeries.C W.a₃ * formalW W)
      = 1 - PowerSeries.C W.a₁ * ζ - PowerSeries.C W.a₃ * (lam0 W * ζ) := by
    rw [hsubsub, hsubsub, h1subst, PowerSeries.subst_mul hζsub,
      PowerSeries.subst_mul hζsub, PowerSeries.subst_X hζsub, hWζ,
      subst_C' ζ hζsub, subst_C' ζ hζsub]
  have hDU : PowerSeries.subst ζ (PowerSeries.mk (invDenom_coeff W))
      * (1 - PowerSeries.C W.a₁ * ζ - PowerSeries.C W.a₃ * (lam0 W * ζ)) = 1 := by
    have h := congrArg (PowerSeries.subst ζ) (invDenom_mul_eq_one W)
    rwa [PowerSeries.subst_mul hζsub, hT, h1subst] at h
  have hadd : formalInverse W + PowerSeries.X * PowerSeries.mk (invDenom_coeff W) = 0 := by
    rw [formalInverse_eq_neg_X_mul]
    exact neg_add_cancel _
  have hzero : PowerSeries.subst (R := R) ζ (0 : PowerSeries R) = 0 := by
    have h := map_zero (PowerSeries.substAlgHom (R := R) hζsub)
    rwa [PowerSeries.coe_substAlgHom hζsub] at h
  have h5 : PowerSeries.subst ζ (formalInverse W)
      + ζ * PowerSeries.subst ζ (PowerSeries.mk (invDenom_coeff W)) = 0 := by
    have h := congrArg (PowerSeries.subst ζ) hadd
    rwa [PowerSeries.subst_add hζsub, PowerSeries.subst_mul hζsub,
      PowerSeries.subst_X hζsub, hzero] at h
  have hstar : -ζ = PowerSeries.X * (1 - PowerSeries.C W.a₁ * ζ
      - PowerSeries.C W.a₃ * (lam0 W * ζ)) := by
    rw [hζ_eq]
    exact star_identity (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃)
      (PowerSeries.C W.a₄) (PowerSeries.C W.a₆) (lam0 W) PowerSeries.X v hv (lam0_eq W)
  exact row_final_abstract (PowerSeries.subst ζ (formalInverse W))
    (PowerSeries.subst ζ (PowerSeries.mk (invDenom_coeff W))) ζ PowerSeries.X
    (1 - PowerSeries.C W.a₁ * ζ - PowerSeries.C W.a₃ * (lam0 W * ζ)) h5 hstar hDU

/-- The row-`s` coefficients of the chord composition are those of `X`. -/
private lemma coeff_single_subst_z3 (s : Fin 2) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single s n)
      (PowerSeries.subst (formalZ3 W) (formalInverse W)) = if n = 1 then 1 else 0 := by
  have hz3 : MvPowerSeries.HasSubst (fun _ : Unit ↦ formalZ3 W) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_formalZ3 W
  have hcomp : MvPowerSeries.subst
      (fun u : Unit ↦ MvPowerSeries.subst (rowFamily (R := R) s)
        ((fun _ : Unit ↦ formalZ3 W) u)) (formalInverse W)
      = PowerSeries.subst
        (MvPowerSeries.subst (rowFamily (R := R) s) (formalZ3 W)) (formalInverse W) := rfl
  rw [← coeff_subst_rowFamily s _ n]
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hz3 (hasSubst_rowFamily s),
    hcomp, subst_rowZ3_formalInverse, PowerSeries.coeff_X]

/-! ### FG-A6: the band check (total degrees 2–4)

The legacy `formalGroupLaw_coeff` hardcodes the nine coefficients of total
degree 2–4; here we compute the corresponding coefficients of the chord
composition through the `bcomp` dictionary and verify they agree (they
match the *corrected* print of [Sil] p. 120 — see the module docstring).
Everything happens in `R` (no power-series arithmetic), by expanding the
finite sums against the small-index values of the streams.
-/

/-- `w₄ = a₁` ([Sil] IV.1.1: `w = z³(1 + A₁z + ⋯)`, `A₁ = a₁`). -/
theorem formalW_coeff_four : formalW_coeff W 4 = W.a₁ := by
  rw [formalW_coeff_eq_step]
  simp [formalW_step, conv₂, conv₃, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three]

/-- `w₅ = a₁² + a₂` ([Sil] IV.1.1: `A₂ = a₁² + a₂`). -/
theorem formalW_coeff_five : formalW_coeff W 5 = W.a₁ ^ 2 + W.a₂ := by
  rw [formalW_coeff_eq_step]
  simp [formalW_step, conv₂, conv₃, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four]
  ring

private lemma AS_00 : AS W 0 0 = 1 := by
  simp [AS, lamS, bmul, formalW_coeff_one]

private lemma AS_10 : AS W 1 0 = 0 := by
  simp [AS, lamS, bmul, Finset.sum_range_succ, formalW_coeff_one, formalW_coeff_two]

private lemma AS_01 : AS W 0 1 = 0 := by
  simp [AS, lamS, bmul, Finset.sum_range_succ, formalW_coeff_one, formalW_coeff_two]

private lemma AS_20 : AS W 2 0 = W.a₂ := by
  simp [AS, lamS, bmul, Finset.sum_range_succ, formalW_coeff_one, formalW_coeff_two,
    formalW_coeff_three]

private lemma AS_11 : AS W 1 1 = W.a₂ := by
  simp [AS, lamS, bmul, Finset.sum_range_succ, formalW_coeff_one, formalW_coeff_two,
    formalW_coeff_three]

private lemma AS_02 : AS W 0 2 = W.a₂ := by
  simp [AS, lamS, bmul, Finset.sum_range_succ, formalW_coeff_one, formalW_coeff_two,
    formalW_coeff_three]

private lemma binvAS_10 : binv (AS W) 1 0 = 0 := by
  rw [binv_eq_of_ne _ _ _ (by simp)]
  simp [Finset.sum_range_succ, AS_10]

private lemma binvAS_01 : binv (AS W) 0 1 = 0 := by
  rw [binv_eq_of_ne _ _ _ (by simp)]
  simp [Finset.sum_range_succ, AS_01]

private lemma binvAS_20 : binv (AS W) 2 0 = -W.a₂ := by
  rw [binv_eq_of_ne _ _ _ (by simp)]
  simp [Finset.sum_range_succ, AS_20, AS_10, binvAS_10]

private lemma binvAS_11 : binv (AS W) 1 1 = -W.a₂ := by
  rw [binv_eq_of_ne _ _ _ (by simp)]
  simp [Finset.sum_range_succ, AS_11, AS_10, AS_01, binvAS_10, binvAS_01]

private lemma binvAS_02 : binv (AS W) 0 2 = -W.a₂ := by
  rw [binv_eq_of_ne _ _ _ (by simp)]
  simp [Finset.sum_range_succ, AS_02, AS_01]

private lemma BS_00 : BS W 0 0 = 0 := by
  simp [BS, lamS, nuS, w1S, bmul, formalW_coeff_zero, formalW_coeff_one]

private lemma BS_10 : BS W 1 0 = 0 := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two]

private lemma BS_01 : BS W 0 1 = 0 := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two]

private lemma BS_20 : BS W 2 0 = W.a₁ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three]

private lemma BS_11 : BS W 1 1 = W.a₁ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three]

private lemma BS_02 : BS W 0 2 = W.a₁ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three]

private lemma BS_30 : BS W 3 0 = W.a₁ ^ 2 := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four]
  ring

private lemma BS_21 : BS W 2 1 = W.a₁ ^ 2 - W.a₂ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four]
  ring

private lemma BS_12 : BS W 1 2 = W.a₁ ^ 2 - W.a₂ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four]
  ring

private lemma BS_03 : BS W 0 3 = W.a₁ ^ 2 := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four]
  ring

private lemma BS_31 : BS W 3 1 = W.a₁ ^ 3 + 2 * W.a₃ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four,
    formalW_coeff_five]
  ring

private lemma BS_22 : BS W 2 2 = W.a₁ ^ 3 + 3 * W.a₃ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four,
    formalW_coeff_five]
  ring

private lemma BS_13 : BS W 1 3 = W.a₁ ^ 3 + 2 * W.a₃ := by
  simp [BS, lamS, nuS, w1S, bmul, Finset.sum_range_succ, formalW_coeff_zero,
    formalW_coeff_one, formalW_coeff_two, formalW_coeff_three, formalW_coeff_four,
    formalW_coeff_five]
  ring

private lemma z3S_00 : z3S W 0 0 = 0 := z3S_zero_zero W

private lemma z3S_10 : z3S W 1 0 = -1 := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10]

private lemma z3S_01 : z3S W 0 1 = -1 := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_01]

private lemma z3S_20 : z3S W 2 0 = -W.a₁ := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_20, binvAS_10]

private lemma z3S_11 : z3S W 1 1 = -W.a₁ := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_01, BS_11, binvAS_10, binvAS_01]

private lemma z3S_02 : z3S W 0 2 = -W.a₁ := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_02, binvAS_01]

private lemma z3S_30 : z3S W 3 0 = -W.a₁ ^ 2 := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_20, BS_30, binvAS_10,
    binvAS_20]

private lemma z3S_21 : z3S W 2 1 = W.a₂ - W.a₁ ^ 2 := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_01, BS_11, BS_20, BS_21,
    binvAS_10, binvAS_01, binvAS_11, binvAS_20]

private lemma z3S_12 : z3S W 1 2 = W.a₂ - W.a₁ ^ 2 := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_01, BS_11, BS_02, BS_12,
    binvAS_10, binvAS_01, binvAS_11, binvAS_02]

private lemma z3S_03 : z3S W 0 3 = -W.a₁ ^ 2 := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_01, BS_03, binvAS_01,
    binvAS_02]

private lemma z3S_31 : z3S W 3 1 = 2 * W.a₁ * W.a₂ - W.a₁ ^ 3 - 2 * W.a₃ := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_01, BS_11, BS_20, BS_21,
    BS_30, BS_31, binvAS_10, binvAS_01, binvAS_11, binvAS_20]
  ring

private lemma z3S_22 : z3S W 2 2 = 3 * W.a₁ * W.a₂ - W.a₁ ^ 3 - 3 * W.a₃ := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_01, BS_11, BS_20, BS_02,
    BS_21, BS_12, BS_22, binvAS_10, binvAS_01, binvAS_11, binvAS_20, binvAS_02]
  ring

private lemma z3S_13 : z3S W 1 3 = 2 * W.a₁ * W.a₂ - W.a₁ ^ 3 - 2 * W.a₃ := by
  simp [z3S, bmul, Finset.sum_range_succ, BS_00, BS_10, BS_01, BS_11, BS_02, BS_12,
    BS_03, BS_13, binvAS_10, binvAS_01, binvAS_11, binvAS_02]
  ring

private lemma bpow_two (f : ℕ → ℕ → R) (i j : ℕ) : bpow f i j 2 = bmul f f i j := by
  have h : bpow f i j 2 = bmul f (fun a b ↦ bpow f a b 1) i j := bpow_succ f i j 1
  rw [h, show (fun a b ↦ bpow f a b 1) = f from funext fun a ↦ funext fun b ↦
    bpow_one f a b]

private lemma bpow_three (f : ℕ → ℕ → R) (i j : ℕ) :
    bpow f i j 3 = bmul f (bmul f f) i j := by
  have h : bpow f i j 3 = bmul f (fun a b ↦ bpow f a b 2) i j := bpow_succ f i j 2
  rw [h, show (fun a b ↦ bpow f a b 2) = bmul f f from funext fun a ↦ funext fun b ↦
    bpow_two f a b]

private lemma bpow_four (f : ℕ → ℕ → R) (i j : ℕ) :
    bpow f i j 4 = bmul f (bmul f (bmul f f)) i j := by
  have h : bpow f i j 4 = bmul f (fun a b ↦ bpow f a b 3) i j := bpow_succ f i j 3
  rw [h, show (fun a b ↦ bpow f a b 3) = bmul f (bmul f f) from funext fun a ↦
    funext fun b ↦ bpow_three f a b]

private lemma band_11 : bcomp (formalInverse_coeff W) (z3S W) 1 1 = -W.a₁ := by
  change ((Finset.range (1 + 1 + 1)).sum fun n ↦
    formalInverse_coeff W n * bpow (z3S W) 1 1 n) = -W.a₁
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    bpow_zero, bpow_one, bpow_two]
  simp [formalInverse_coeff, invDenom_coeff_one, bmul, Finset.sum_range_succ,
    z3S_00, z3S_10, z3S_01, z3S_11]
  ring

private lemma band_21 : bcomp (formalInverse_coeff W) (z3S W) 2 1 = -W.a₂ := by
  change ((Finset.range (2 + 1 + 1)).sum fun n ↦
    formalInverse_coeff W n * bpow (z3S W) 2 1 n) = -W.a₂
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, bpow_zero, bpow_one, bpow_two, bpow_three]
  simp [formalInverse_coeff, invDenom_coeff_one, invDenom_coeff_two, bmul,
    Finset.sum_range_succ, z3S_00, z3S_10, z3S_01, z3S_11, z3S_20, z3S_21]
  ring

private lemma band_12 : bcomp (formalInverse_coeff W) (z3S W) 1 2 = -W.a₂ := by
  change ((Finset.range (1 + 2 + 1)).sum fun n ↦
    formalInverse_coeff W n * bpow (z3S W) 1 2 n) = -W.a₂
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, bpow_zero, bpow_one, bpow_two, bpow_three]
  simp [formalInverse_coeff, invDenom_coeff_one, invDenom_coeff_two, bmul,
    Finset.sum_range_succ, z3S_00, z3S_10, z3S_01, z3S_11, z3S_02, z3S_12]
  ring

private lemma band_31 : bcomp (formalInverse_coeff W) (z3S W) 3 1 = -(2 * W.a₃) := by
  change ((Finset.range (3 + 1 + 1)).sum fun n ↦
    formalInverse_coeff W n * bpow (z3S W) 3 1 n) = -(2 * W.a₃)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, bpow_zero, bpow_one, bpow_two,
    bpow_three, bpow_four]
  simp [formalInverse_coeff, invDenom_coeff_one, invDenom_coeff_two,
    invDenom_coeff_three, bmul, Finset.sum_range_succ, z3S_00, z3S_10, z3S_01, z3S_11,
    z3S_20, z3S_21, z3S_30, z3S_31]
  ring

private lemma band_22 : bcomp (formalInverse_coeff W) (z3S W) 2 2
    = W.a₁ * W.a₂ - 3 * W.a₃ := by
  change ((Finset.range (2 + 2 + 1)).sum fun n ↦
    formalInverse_coeff W n * bpow (z3S W) 2 2 n) = W.a₁ * W.a₂ - 3 * W.a₃
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, bpow_zero, bpow_one, bpow_two,
    bpow_three, bpow_four]
  simp [formalInverse_coeff, invDenom_coeff_one, invDenom_coeff_two,
    invDenom_coeff_three, bmul, Finset.sum_range_succ, z3S_00, z3S_10, z3S_01, z3S_11,
    z3S_20, z3S_02, z3S_21, z3S_12, z3S_22]
  ring

private lemma band_13 : bcomp (formalInverse_coeff W) (z3S W) 1 3 = -(2 * W.a₃) := by
  change ((Finset.range (1 + 3 + 1)).sum fun n ↦
    formalInverse_coeff W n * bpow (z3S W) 1 3 n) = -(2 * W.a₃)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, bpow_zero, bpow_one, bpow_two,
    bpow_three, bpow_four]
  simp [formalInverse_coeff, invDenom_coeff_one, invDenom_coeff_two,
    invDenom_coeff_three, bmul, Finset.sum_range_succ, z3S_00, z3S_10, z3S_01, z3S_11,
    z3S_02, z3S_12, z3S_03, z3S_13]
  ring

/-! ### FG-A6: the spec theorem -/

/-- **The spec of the legacy formal group law** (FG-A6, Silverman IV §1
pp. 119–120): the coefficient-level construction `formalGroupLaw` *is* the
chord composition `i ∘ z₃` of the inversion series with the third root of
the chord cubic. The unit rows are the row identities proven above, the
total-degree-2–4 band is the finite check against the hardcoded values
(matching the corrected print), and all higher coefficients are the
`bcomp` branch, identified through the FG-A4 dictionary. -/
theorem formalGroupLaw_eq_chord :
    (formalGroupLaw W).toMvPowerSeries
      = PowerSeries.subst (formalZ3 W) (formalInverse W) := by
  have hbc : ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d (PowerSeries.subst (formalZ3 W) (formalInverse W))
        = bcomp (formalInverse_coeff W) (z3S W) (d 0) (d 1) := fun d ↦ by
    rw [← F_of_z3S, show formalInverse W = PowerSeries.mk (formalInverse_coeff W) from rfl,
      coeff_subst_F_of _ _ (z3S_zero_zero W)]
  apply MvPowerSeries.ext fun d ↦ ?_
  rw [coeff_formalGroupLaw]
  by_cases h0 : d 0 = 0
  · have hd : d = Finsupp.single 1 (d 1) := (fin2_eq_single_one_iff d).mpr h0
    rw [show (MvPowerSeries.coeff d) (PowerSeries.subst (formalZ3 W) (formalInverse W))
        = if d 1 = 1 then 1 else 0 from by
          conv_lhs => rw [hd]
          exact coeff_single_subst_z3 W 1 (d 1)]
    simp only [formalGroupLaw_coeff]
    rw [if_pos h0]
  · by_cases h1 : d 1 = 0
    · have hd : d = Finsupp.single 0 (d 0) := (fin2_eq_single_zero_iff d).mpr h1
      rw [show (MvPowerSeries.coeff d) (PowerSeries.subst (formalZ3 W) (formalInverse W))
          = if d 0 = 1 then 1 else 0 from by
            conv_lhs => rw [hd]
            exact coeff_single_subst_z3 W 0 (d 0)]
      simp only [formalGroupLaw_coeff]
      rw [if_neg h0, if_pos h1]
    · rw [hbc d]
      by_cases h2 : d 0 + d 1 = 2
      · have e0 : d 0 = 1 := by omega
        have e1 : d 1 = 1 := by omega
        simp only [formalGroupLaw_coeff]
        rw [if_neg h0, if_neg h1, if_pos h2, e0, e1, band_11]
      · by_cases h3 : d 0 + d 1 = 3
        · rcases (by omega : d 0 = 2 ∧ d 1 = 1 ∨ d 0 = 1 ∧ d 1 = 2) with ⟨e0, e1⟩ | ⟨e0, e1⟩
          · simp only [formalGroupLaw_coeff]
            rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3, e0, e1, band_21]
          · simp only [formalGroupLaw_coeff]
            rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3, e0, e1, band_12]
        · by_cases h4 : d 0 + d 1 = 4
          · rcases (by omega : d 0 = 3 ∧ d 1 = 1 ∨ d 0 = 2 ∧ d 1 = 2 ∨ d 0 = 1 ∧ d 1 = 3)
              with ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩
            · simp only [formalGroupLaw_coeff]
              rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, e0, e1,
                if_neg (by omega), band_31]
            · simp only [formalGroupLaw_coeff]
              rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, e0, e1,
                if_pos ⟨rfl, rfl⟩, band_22]
            · simp only [formalGroupLaw_coeff]
              rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, e0, e1,
                if_neg (by omega), band_13]
          · exact formalGroupLaw_coeff_tail W d h0 h1 h2 h3 h4

end HasseWeil

module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogAdditivity
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLogHomogeneous

/-!
# Additivity of the conductor-flexible finite logarithm

This file ports the setup-dependent finite-log additivity proof to
`ConductorFlexibleFullTeichStickelbergerSetup`, reusing the shared formal
power-series identities from `FiniteLogAdditivity`.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open PowerSeries

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

namespace Private

def formalProductArgPoly (x y : R') : Polynomial R' :=
  Polynomial.X * Polynomial.C x + Polynomial.X * Polynomial.C y +
    Polynomial.X ^ 2 * Polynomial.C (x * y)

omit [NumberField R'] in
theorem formalProductArgPoly_coe (x y : R') :
    ((formalProductArgPoly x y : Polynomial R') : PowerSeries R') =
      PowerSeries.X * PowerSeries.C x +
        PowerSeries.X * PowerSeries.C y +
        PowerSeries.X ^ 2 * PowerSeries.C (x * y) := by
  simp [formalProductArgPoly]
  ring_nf

omit [NumberField R'] in
theorem finiteLogProductArgPoly_map_eq_formal (x y : 𝓞 R') :
    (finiteLogProductArgPoly x y).map (algebraMap (𝓞 R') R') =
      formalProductArgPoly (x : R') (y : R') := by
  simp [finiteLogProductArgPoly, formalProductArgPoly, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring_nf

omit [NumberField R'] in
theorem finiteLogProductArgPoly_coe_eq_formal (x y : 𝓞 R') :
    (((finiteLogProductArgPoly x y).map (algebraMap (𝓞 R') R') : Polynomial R') :
      PowerSeries R') =
      PowerSeries.X * PowerSeries.C (x : R') +
        PowerSeries.X * PowerSeries.C (y : R') +
        PowerSeries.X ^ 2 * PowerSeries.C ((x * y : 𝓞 R') : R') := by
  rw [finiteLogProductArgPoly_map_eq_formal]
  exact formalProductArgPoly_coe (x : R') (y : R')

def finiteLogAdditivityNumerator (x y : 𝓞 R') (d n : ℕ) : 𝓞 R' :=
  ((-1 : 𝓞 R') ^ (n + 1)) *
    (((((finiteLogProductArgPoly x y) ^ n).coeff d +
      -(((finiteLogProductArgPoly x 0) ^ n).coeff d)) +
      -(((finiteLogProductArgPoly y 0) ^ n).coeff d)))

theorem finiteLogAdditivityNumerator_mem_Q_pow {x y : 𝓞 R'}
    (hx : x ∈ F.Q) (hy : y ∈ F.Q) (d n : ℕ) :
    finiteLogAdditivityNumerator x y d n ∈ F.Q ^ d := by
  have hprod :
      ((finiteLogProductArgPoly x y) ^ n).coeff d ∈ F.Q ^ d :=
    finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d
  have hxlin :
      ((finiteLogProductArgPoly x 0) ^ n).coeff d ∈ F.Q ^ d :=
    finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx (zero_mem F.Q) n d
  have hylin :
      ((finiteLogProductArgPoly y 0) ^ n).coeff d ∈ F.Q ^ d :=
    finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hy (zero_mem F.Q) n d
  exact Ideal.mul_mem_left _ _
    ((F.Q ^ d).add_mem ((F.Q ^ d).add_mem hprod ((F.Q ^ d).neg_mem hxlin))
      ((F.Q ^ d).neg_mem hylin))

omit [NumberField R'] in
theorem finiteLogProductArgPoly_coeff_zero (x y : 𝓞 R') :
    (finiteLogProductArgPoly x y).coeff 0 = 0 := by
  simp [finiteLogProductArgPoly, Polynomial.coeff_monomial]

omit [NumberField R'] in
theorem finiteLogProductArgPoly_map_coeff_zero (x y : 𝓞 R') :
    ((finiteLogProductArgPoly x y).map (algebraMap (𝓞 R') R')).coeff 0 = 0 := by
  simp [Polynomial.coeff_map, finiteLogProductArgPoly_coeff_zero]

omit [NumberField R'] in
theorem finiteLogProductArgPoly_pow_coeff_eq_zero_of_lt (x y : 𝓞 R')
    {n d : ℕ} (hdn : d < n) :
    ((finiteLogProductArgPoly x y) ^ n).coeff d = 0 := by
  have h :=
    FiniteLogFormal.coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero
      (finiteLogProductArgPoly x y) (finiteLogProductArgPoly_coeff_zero x y) hdn
  simpa [← Polynomial.coe_pow, Polynomial.coeff_coe] using h

theorem finiteLogAdditivity_rational_sum_eq_zero (x y : 𝓞 R') (d : ℕ) :
    (∑ n ∈ Finset.Icc 1 d,
      algebraMap ℚ R' (((-1 : ℚ) ^ (n + 1)) / n) *
        (((algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x y) ^ n).coeff d) -
          (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x 0) ^ n).coeff d)) -
          (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly y 0) ^ n).coeff d))) = 0 := by
  classical
  let Pxy : Polynomial R' := (finiteLogProductArgPoly x y).map (algebraMap (𝓞 R') R')
  let Px : Polynomial R' := (finiteLogProductArgPoly x 0).map (algebraMap (𝓞 R') R')
  let Py : Polynomial R' := (finiteLogProductArgPoly y 0).map (algebraMap (𝓞 R') R')
  have hxyarg :
      (Pxy : PowerSeries R') =
        PowerSeries.X * PowerSeries.C (x : R') +
          PowerSeries.X * PowerSeries.C (y : R') +
          PowerSeries.X ^ 2 * PowerSeries.C ((x : R') * (y : R')) := by
    simpa [Pxy, map_mul] using finiteLogProductArgPoly_coe_eq_formal (x := x) (y := y)
  have hxarg :
      (Px : PowerSeries R') = PowerSeries.X * PowerSeries.C (x : R') := by
    simpa [Px] using finiteLogProductArgPoly_coe_eq_formal (x := x) (y := (0 : 𝓞 R'))
  have hyarg :
      (Py : PowerSeries R') = PowerSeries.X * PowerSeries.C (y : R') := by
    simpa [Py] using finiteLogProductArgPoly_coe_eq_formal (x := y) (y := (0 : 𝓞 R'))
  have hformal :=
    FiniteLogFormal.coeff_log_subst_add_add_mul_scaled (A := R') (x : R') (y : R') d
  rw [← hxyarg, ← hxarg, ← hyarg] at hformal
  have hPxy0 : Pxy.coeff 0 = 0 := by
    simpa [Pxy] using finiteLogProductArgPoly_map_coeff_zero (x := x) (y := y)
  have hPx0 : Px.coeff 0 = 0 := by
    simpa [Px] using finiteLogProductArgPoly_map_coeff_zero (x := x) (y := (0 : 𝓞 R'))
  have hPy0 : Py.coeff 0 = 0 := by
    simpa [Py] using finiteLogProductArgPoly_map_coeff_zero (x := y) (y := (0 : 𝓞 R'))
  rw [FiniteLogFormal.coeff_subst_log_coe_eq_sum_Icc Pxy hPxy0 d,
    FiniteLogFormal.coeff_subst_log_coe_eq_sum_Icc Px hPx0 d,
    FiniteLogFormal.coeff_subst_log_coe_eq_sum_Icc Py hPy0 d] at hformal
  simp only [Pxy, Px, Py, FiniteLogFormal.coeff_coe_map_pow] at hformal
  calc
    (∑ n ∈ Finset.Icc 1 d,
      algebraMap ℚ R' (((-1 : ℚ) ^ (n + 1)) / n) *
        (((algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x y) ^ n).coeff d) -
          (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x 0) ^ n).coeff d)) -
          (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly y 0) ^ n).coeff d)))
        =
      (∑ n ∈ Finset.Icc 1 d,
        algebraMap ℚ R' (((-1 : ℚ) ^ (n + 1)) / n) *
          (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x y) ^ n).coeff d)) -
        (∑ n ∈ Finset.Icc 1 d,
          algebraMap ℚ R' (((-1 : ℚ) ^ (n + 1)) / n) *
            (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x 0) ^ n).coeff d)) -
        (∑ n ∈ Finset.Icc 1 d,
          algebraMap ℚ R' (((-1 : ℚ) ^ (n + 1)) / n) *
            (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly y 0) ^ n).coeff d)) := by
        simp [Finset.sum_sub_distrib, mul_sub]
    _ = 0 := by
        rw [hformal]
        ring

theorem finiteLogAdditivity_factorial_weighted_sum_eq_zero
    (x y : 𝓞 R') (d : ℕ) :
    (∑ n ∈ Finset.Icc 1 d,
      ((d.factorial / n : ℕ) : 𝓞 R') * finiteLogAdditivityNumerator x y d n) = 0 := by
  classical
  apply NumberField.RingOfIntegers.coe_injective (K := R')
  rw [map_zero]
  have hrat := finiteLogAdditivity_rational_sum_eq_zero (R' := R') x y d
  calc
    (algebraMap (𝓞 R') R')
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : 𝓞 R') * finiteLogAdditivityNumerator x y d n)
        =
      ∑ n ∈ Finset.Icc 1 d,
        ((d.factorial : R') *
          (algebraMap ℚ R' (((-1 : ℚ) ^ (n + 1)) / n) *
            (((algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x y) ^ n).coeff d) -
              (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x 0) ^ n).coeff d)) -
              (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly y 0) ^ n).coeff d)))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
        have hdiv :
            ((d.factorial / n : ℕ) : R') = (d.factorial : R') / (n : R') :=
          Nat.cast_div_charZero (K := R')
            (Nat.dvd_factorial (Nat.pos_of_ne_zero (Nat.ne_zero_of_lt hn1)) hnd)
        have hn0 : (n : R') ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn1)
        simp [finiteLogAdditivityNumerator, hdiv]
        field_simp [hn0]
        ring
    _ =
      (d.factorial : R') *
        (∑ n ∈ Finset.Icc 1 d,
          algebraMap ℚ R' (((-1 : ℚ) ^ (n + 1)) / n) *
            (((algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x y) ^ n).coeff d) -
              (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly x 0) ^ n).coeff d)) -
              (algebraMap (𝓞 R') R') (((finiteLogProductArgPoly y 0) ^ n).coeff d))) := by
        rw [Finset.mul_sum]
    _ = 0 := by
        rw [hrat, mul_zero]

theorem finiteLogAdditivity_den_exponent_le {n d : ℕ} (hn : n ≠ 0) (hnd : n ≤ d) :
    n.factorization ℓ * (ℓ - 1) ≤ d := by
  have h := Nat.factorization_mul_pred_le_pred
    (ell := ℓ) (n := n) (Fact.out : Nat.Prime ℓ) hn
  omega

theorem finiteLogAdditivity_degree_sum_eq_zero (N d : ℕ)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    (∑ a ∈ (Finset.Icc 1 d).attach,
      F.finiteLogNatDivEvalAtDegree N a.1 d
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (finiteLogAdditivityNumerator x y d a.1)
        (finiteLogAdditivityNumerator_mem_Q_pow (F := F) hx hy d a.1)
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
          exact finiteLogAdditivity_den_exponent_le (ℓ := ℓ)
            (Nat.ne_zero_of_lt ha1) had)) = 0 := by
  classical
  let z : ℕ → 𝓞 R' := fun n => finiteLogAdditivityNumerator x y d n
  have hz0 : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + 0) := by
    intro n hnI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
    have hden : n.factorization ℓ * (ℓ - 1) ≤ d :=
      finiteLogAdditivity_den_exponent_le (ℓ := ℓ) (Nat.ne_zero_of_lt hn1) hnd
    simpa using
      (Ideal.pow_le_pow_right hden
        (finiteLogAdditivityNumerator_mem_Q_pow (F := F) hx hy d n))
  have htransport :=
    F.finiteLogNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_eq_zero
      (N := N) (d := d) (s := 0) z hz0
      (by
        simpa [z] using
          (finiteLogAdditivity_factorial_weighted_sum_eq_zero (R' := R') x y d))
  calc
    (∑ a ∈ (Finset.Icc 1 d).attach,
      F.finiteLogNatDivEvalAtDegree N a.1 d
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (finiteLogAdditivityNumerator x y d a.1)
        (finiteLogAdditivityNumerator_mem_Q_pow (F := F) hx hy d a.1)
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
          exact finiteLogAdditivity_den_exponent_le (ℓ := ℓ)
            (Nat.ne_zero_of_lt ha1) had))
        =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [z]
        exact F.finiteLogNatDivEvalAtDegree_eq_finiteLogNatDivEval
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (finiteLogAdditivityNumerator_mem_Q_pow (F := F) hx hy d a.1)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            exact finiteLogAdditivity_den_exponent_le (ℓ := ℓ)
              (Nat.ne_zero_of_lt ha1) had)
          (hz0 a.1 a.2)
    _ = 0 := htransport

theorem finiteLogAdditivity_term_eq (N d n : ℕ) (hn : n ≠ 0) (hnd : n ≤ d)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    F.finiteLogNatDivEvalAtDegree N n d hn
        (finiteLogAdditivityNumerator x y d n)
        (finiteLogAdditivityNumerator_mem_Q_pow (F := F) hx hy d n)
        (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
      =
    ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        F.finiteLogNatDivEvalAtDegree N n d hn
          (((finiteLogProductArgPoly x y) ^ n).coeff d)
          (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
          (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd) -
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        F.finiteLogNatDivEvalAtDegree N n d hn
          (((finiteLogProductArgPoly x 0) ^ n).coeff d)
          (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx (zero_mem F.Q) n d)
          (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd) -
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        F.finiteLogNatDivEvalAtDegree N n d hn
          (((finiteLogProductArgPoly y 0) ^ n).coeff d)
          (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hy (zero_mem F.Q) n d)
          (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd) := by
  let zxy : 𝓞 R' := ((finiteLogProductArgPoly x y) ^ n).coeff d
  let zx : 𝓞 R' := ((finiteLogProductArgPoly x 0) ^ n).coeff d
  let zy : 𝓞 R' := ((finiteLogProductArgPoly y 0) ^ n).coeff d
  let s : 𝓞 R' := (-1 : 𝓞 R') ^ (n + 1)
  let hden : n.factorization ℓ * (ℓ - 1) ≤ d :=
    finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd
  have hzxy : zxy ∈ F.Q ^ d :=
    finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d
  have hzx : zx ∈ F.Q ^ d :=
    finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx (zero_mem F.Q) n d
  have hzy : zy ∈ F.Q ^ d :=
    finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hy (zero_mem F.Q) n d
  have hsubx : zxy + -zx ∈ F.Q ^ d := (F.Q ^ d).add_mem hzxy ((F.Q ^ d).neg_mem hzx)
  have hsubxy : (zxy + -zx) + -zy ∈ F.Q ^ d :=
    (F.Q ^ d).add_mem hsubx ((F.Q ^ d).neg_mem hzy)
  have hs_sub : s * ((zxy + -zx) + -zy) ∈ F.Q ^ d :=
    Ideal.mul_mem_left _ s hsubxy
  have hnum :
      finiteLogAdditivityNumerator x y d n = s * ((zxy + -zx) + -zy) := by
    rfl
  have hmk_s :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) s =
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) := by
    simp [s]
  calc
    F.finiteLogNatDivEvalAtDegree N n d hn
        (finiteLogAdditivityNumerator x y d n)
        (finiteLogAdditivityNumerator_mem_Q_pow (F := F) hx hy d n)
        (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
        =
      F.finiteLogNatDivEvalAtDegree N n d hn
        (s * ((zxy + -zx) + -zy)) hs_sub hden := by
        cases hnum
        rfl
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) s *
        F.finiteLogNatDivEvalAtDegree N n d hn ((zxy + -zx) + -zy) hsubxy hden :=
        F.finiteLogNatDivEvalAtDegree_mul_left hn s hsubxy hs_sub hden
    _ =
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        (F.finiteLogNatDivEvalAtDegree N n d hn zxy hzxy hden -
          F.finiteLogNatDivEvalAtDegree N n d hn zx hzx hden -
          F.finiteLogNatDivEvalAtDegree N n d hn zy hzy hden) := by
        rw [hmk_s]
        rw [F.finiteLogNatDivEvalAtDegree_add hn hsubx ((F.Q ^ d).neg_mem hzy) hsubxy hden]
        rw [F.finiteLogNatDivEvalAtDegree_add hn hzxy ((F.Q ^ d).neg_mem hzx) hsubx hden]
        rw [F.finiteLogNatDivEvalAtDegree_neg hn hzx ((F.Q ^ d).neg_mem hzx) hden]
        rw [F.finiteLogNatDivEvalAtDegree_neg hn hzy ((F.Q ^ d).neg_mem hzy) hden]
        ring
    _ = _ := by
        ring

noncomputable def finiteLogProductHomogeneousGrid (N : ℕ) (x y : 𝓞 R')
    (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
    if hn : n = 0 then 0 else
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
          if hnd : n ≤ d then
            F.finiteLogNatDivEvalAtDegree N n d hn
              (((finiteLogProductArgPoly x y) ^ n).coeff d)
              (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
              (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
          else 0

theorem finiteLogProductHomogeneousGrid_eq_degree_sum (N : ℕ)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    finiteLogProductHomogeneousGrid (F := F) N x y hx hy =
      ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
          if hn : n = 0 then 0 else
            ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                F.finiteLogNatDivEvalAtDegree N n d hn
                  (((finiteLogProductArgPoly x y) ^ n).coeff d)
                  (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
                  (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
              else 0) := by
  classical
  calc
    finiteLogProductHomogeneousGrid (F := F) N x y hx hy
        =
      ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
          if hn : n = 0 then 0 else
            ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                F.finiteLogNatDivEvalAtDegree N n d hn
                  (((finiteLogProductArgPoly x y) ^ n).coeff d)
                  (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
                  (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
              else 0) := by
        refine Finset.sum_congr rfl ?_
        intro n _hnC
        by_cases hn0 : n = 0
        · simp [hn0]
        · simp [hn0, Finset.mul_sum]
    _ =
      ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
          if hn : n = 0 then 0 else
            ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                F.finiteLogNatDivEvalAtDegree N n d hn
                  (((finiteLogProductArgPoly x y) ^ n).coeff d)
                  (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
                  (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
              else 0) := by
        rw [Finset.sum_comm]

theorem finiteLogProductHomogeneousGrid_degree_sub_eq_zero (N d : ℕ)
    (hd : d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N))
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    (∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
      ((if hn : n = 0 then 0 else
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            F.finiteLogNatDivEvalAtDegree N n d hn
              (((finiteLogProductArgPoly x y) ^ n).coeff d)
              (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
              (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            F.finiteLogNatDivEvalAtDegree N n d hn
              (((finiteLogProductArgPoly x 0) ^ n).coeff d)
              (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx (zero_mem F.Q) n d)
              (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            F.finiteLogNatDivEvalAtDegree N n d hn
              (((finiteLogProductArgPoly y 0) ^ n).coeff d)
              (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hy (zero_mem F.Q) n d)
              (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
          else 0)))) = 0 := by
  classical
  let C : ℕ := finiteLogCutoff (ℓ := ℓ) N
  have hdC : d < C := by simpa [C] using hd
  have hsubset : Finset.Icc 1 d ⊆ Finset.range C := fun n hnI =>
    Finset.mem_range.mpr (lt_of_le_of_lt (Finset.mem_Icc.mp hnI).2 hdC)
  let f : ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1) := fun n =>
      (if hn : n = 0 then 0 else
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            F.finiteLogNatDivEvalAtDegree N n d hn
              (((finiteLogProductArgPoly x y) ^ n).coeff d)
              (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
              (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            F.finiteLogNatDivEvalAtDegree N n d hn
              (((finiteLogProductArgPoly x 0) ^ n).coeff d)
              (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx (zero_mem F.Q) n d)
              (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            F.finiteLogNatDivEvalAtDegree N n d hn
              (((finiteLogProductArgPoly y 0) ^ n).coeff d)
              (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hy (zero_mem F.Q) n d)
              (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
          else 0))
  have hzero_out : ∀ n ∈ Finset.range C, n ∉ Finset.Icc 1 d → f n = 0 := by
    intro n hnC hnI
    by_cases hn0 : n = 0
    · simp [f, hn0]
    · have hnle0 : ¬ n ≤ d := by
        intro hnd
        have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
        exact hnI (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
      simp [f, hn0, hnle0]
  calc
    (∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N), f n)
        = ∑ n ∈ Finset.Icc 1 d, f n := by
        rw [show Finset.range (finiteLogCutoff (ℓ := ℓ) N) = Finset.range C by rfl]
        exact (Finset.sum_subset hsubset hzero_out).symm
    _ =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEvalAtDegree N a.1 d
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (finiteLogAdditivityNumerator x y d a.1)
          (finiteLogAdditivityNumerator_mem_Q_pow (F := F) hx hy d a.1)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            exact finiteLogAdditivity_den_exponent_le (ℓ := ℓ)
              (Nat.ne_zero_of_lt ha1) had) := by
        rw [← Finset.sum_attach]
        refine Finset.sum_congr rfl ?_
        intro a _ha
        have hn1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
        have hnd : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
        have hn0 : a.1 ≠ 0 := Nat.ne_zero_of_lt hn1
        simp [f, hn0, hnd, finiteLogAdditivity_term_eq (F := F) N d a.1 hn0 hnd hx hy]
    _ = 0 := finiteLogAdditivity_degree_sum_eq_zero (F := F) N d hx hy

theorem finiteLogProductHomogeneousGrid_add (N : ℕ)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    finiteLogProductHomogeneousGrid (F := F) N x y hx hy =
      finiteLogProductHomogeneousGrid (F := F) N x 0 hx (zero_mem F.Q) +
        finiteLogProductHomogeneousGrid (F := F) N y 0 hy (zero_mem F.Q) := by
  classical
  rw [← sub_eq_zero]
  rw [sub_add_eq_sub_sub]
  calc
    finiteLogProductHomogeneousGrid (F := F) N x y hx hy -
      finiteLogProductHomogeneousGrid (F := F) N x 0 hx (zero_mem F.Q) -
        finiteLogProductHomogeneousGrid (F := F) N y 0 hy (zero_mem F.Q)
        =
      ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
          ((if hn : n = 0 then 0 else
            ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                F.finiteLogNatDivEvalAtDegree N n d hn
                  (((finiteLogProductArgPoly x y) ^ n).coeff d)
                  (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
                  (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
              else 0)) -
          (if hn : n = 0 then 0 else
            ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                F.finiteLogNatDivEvalAtDegree N n d hn
                  (((finiteLogProductArgPoly x 0) ^ n).coeff d)
                  (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx (zero_mem F.Q) n d)
                  (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
              else 0)) -
          (if hn : n = 0 then 0 else
            ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                F.finiteLogNatDivEvalAtDegree N n d hn
                  (((finiteLogProductArgPoly y 0) ^ n).coeff d)
                  (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hy (zero_mem F.Q) n d)
                  (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
              else 0))) := by
        rw [finiteLogProductHomogeneousGrid_eq_degree_sum (F := F) N hx hy]
        rw [finiteLogProductHomogeneousGrid_eq_degree_sum (F := F) N hx (zero_mem F.Q)]
        rw [finiteLogProductHomogeneousGrid_eq_degree_sum (F := F) N hy (zero_mem F.Q)]
        simp [Finset.sum_sub_distrib]
    _ = 0 :=
        Finset.sum_eq_zero fun d hd =>
          finiteLogProductHomogeneousGrid_degree_sub_eq_zero (F := F) N d hd hx hy

theorem finiteLogProductHomogeneousGrid_term_eq (N n : ℕ) (hn : n ≠ 0)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hden0 : n.factorization ℓ * (ℓ - 1) ≤ n) :
    F.finiteLogNatDivEvalAtDegree N n n hn ((finiteLogProductCoord x y) ^ n)
        (Ideal.pow_mem_pow (F.finiteLogProductCoord_mem_Q hx hy) n)
        hden0
      =
    ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
      if hnd : n ≤ d then
        F.finiteLogNatDivEvalAtDegree N n d hn
          (((finiteLogProductArgPoly x y) ^ n).coeff d)
          (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
          (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
      else 0 := by
  classical
  let P : Polynomial (𝓞 R') := (finiteLogProductArgPoly x y) ^ n
  let C : ℕ := finiteLogCutoff (ℓ := ℓ) N
  let den : ℕ := n.factorization ℓ * (ℓ - 1)
  let s : ℕ := n - den
  have hdenn : den ≤ n := by
    simpa [den] using hden0
  have hcoord_sum :
      (finiteLogProductCoord x y) ^ n =
        ∑ d ∈ Finset.range (P.natDegree + 1),
          if n ≤ d then P.coeff d else 0 := by
    calc
      (finiteLogProductCoord x y) ^ n = P.eval 1 := by
        simpa [P] using (finiteLogProductArgPoly_pow_eval_one n x y).symm
      _ = ∑ d ∈ Finset.range (P.natDegree + 1), P.coeff d := by
        rw [Polynomial.eval_eq_sum_range]
        simp
      _ = ∑ d ∈ Finset.range (P.natDegree + 1),
          if n ≤ d then P.coeff d else 0 := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        by_cases hnd : n ≤ d
        · simp [hnd]
        · have hdn : d < n := Nat.lt_of_not_ge hnd
          have hcoeff : P.coeff d = 0 := by
            simpa [P] using finiteLogProductArgPoly_pow_coeff_eq_zero_of_lt x y hdn
          simp [hnd, hcoeff]
  have hcoeff_mem_n : ∀ d, (if n ≤ d then P.coeff d else 0) ∈ F.Q ^ n := by
    intro d
    by_cases hnd : n ≤ d
    · have hd_mem : P.coeff d ∈ F.Q ^ d := by
        simpa [P] using finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d
      simpa [hnd] using Ideal.pow_le_pow_right hnd hd_mem
    · simp [hnd]
  have hcoeff_mem_s :
      ∀ d, (if n ≤ d then P.coeff d else 0) ∈ F.Q ^ (den + s) := by
    intro d
    simpa [s, Nat.add_sub_of_le hdenn] using hcoeff_mem_n d
  have hsum_mem_n :
      (∑ d ∈ Finset.range (P.natDegree + 1), if n ≤ d then P.coeff d else 0) ∈
        F.Q ^ n :=
    Ideal.sum_mem _ fun d _hd => hcoeff_mem_n d
  have hsum_mem_s :
      (∑ d ∈ Finset.range (P.natDegree + 1), if n ≤ d then P.coeff d else 0) ∈
        F.Q ^ (den + s) := by
    simpa [s, Nat.add_sub_of_le hdenn] using hsum_mem_n
  let g : ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1) := fun d =>
    if hnd : n ≤ d then
      F.finiteLogNatDivEvalAtDegree N n d hn (P.coeff d)
        (by
          simpa [P] using finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
        (by
          simpa [den] using finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
    else 0
  have hsplit :
      F.finiteLogNatDivEvalAtDegree N n n hn ((finiteLogProductCoord x y) ^ n)
        (Ideal.pow_mem_pow (F.finiteLogProductCoord_mem_Q hx hy) n)
        hden0
        =
      ∑ d ∈ Finset.range (P.natDegree + 1), g d := by
    calc
      F.finiteLogNatDivEvalAtDegree N n n hn ((finiteLogProductCoord x y) ^ n)
        (Ideal.pow_mem_pow (F.finiteLogProductCoord_mem_Q hx hy) n)
        hden0
          =
        F.finiteLogNatDivEval N n s hn ((finiteLogProductCoord x y) ^ n)
          (by
            simpa [den, s, Nat.add_sub_of_le hdenn] using
              Ideal.pow_mem_pow (F.finiteLogProductCoord_mem_Q hx hy) n) := by
        rw [finiteLogNatDivEvalAtDegree]
      _ =
        F.finiteLogNatDivEval N n s hn
          (∑ d ∈ Finset.range (P.natDegree + 1), if n ≤ d then P.coeff d else 0)
          hsum_mem_s :=
        F.finiteLogNatDivEval_eq_of_eq (N := N) (n := n) (s := s) hn hcoord_sum
          (by
            simpa [den, s, Nat.add_sub_of_le hdenn] using
              Ideal.pow_mem_pow (F.finiteLogProductCoord_mem_Q hx hy) n)
          hsum_mem_s
      _ =
        ∑ d ∈ Finset.range (P.natDegree + 1),
          F.finiteLogNatDivEval N n s hn (if n ≤ d then P.coeff d else 0)
            (hcoeff_mem_s d) := by
        rw [F.finiteLogNatDivEval_sum (N := N) (n := n) (s := s) hn
          (Finset.range (P.natDegree + 1)) (fun d => if n ≤ d then P.coeff d else 0)
          hcoeff_mem_s hsum_mem_s]
      _ = ∑ d ∈ Finset.range (P.natDegree + 1), g d := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        by_cases hnd : n ≤ d
        · have hmem_d : P.coeff d ∈ F.Q ^ d := by
            simpa [P] using finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d
          have hden_d : den ≤ d := by
            simpa [den] using finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd
          have hmem_s : P.coeff d ∈ F.Q ^ (den + s) := by
            simpa [hnd] using hcoeff_mem_s d
          simp only [g, hnd, ↓reduceIte, ↓reduceDIte]
          exact (F.finiteLogNatDivEvalAtDegree_eq_finiteLogNatDivEval
            (N := N) (n := n) (d := d) (s := s) hn hmem_d hden_d hmem_s).symm
        · have hzero_s : (0 : 𝓞 R') ∈ F.Q ^ (den + s) := zero_mem _
          simp [g, hnd, F.finiteLogNatDivEval_zero (N := N) (n := n) (s := s) hn hzero_s]
  let M : ℕ := max (P.natDegree + 1) C
  have hPsubset : Finset.range (P.natDegree + 1) ⊆ Finset.range M := fun d hd =>
    Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hd) (Nat.le_max_left _ _))
  have hCsubset : Finset.range C ⊆ Finset.range M := fun d hd =>
    Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hd) (Nat.le_max_right _ _))
  have hP_to_M :
      (∑ d ∈ Finset.range (P.natDegree + 1), g d) =
        ∑ d ∈ Finset.range M, g d :=
    Finset.sum_subset hPsubset (by
      intro d _hdM hdP
      by_cases hnd : n ≤ d
      · have hd_gt : P.natDegree < d := by
          have hd_not_lt : ¬ d < P.natDegree + 1 := fun hdlt =>
            hdP (Finset.mem_range.mpr hdlt)
          have hle : P.natDegree + 1 ≤ d := Nat.le_of_not_gt hd_not_lt
          omega
        have hcoeff : P.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hd_gt
        have hden_d : den ≤ d := by
          simpa [den] using finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd
        simpa [g, hnd, hcoeff] using
          F.finiteLogNatDivEvalAtDegree_zero (N := N) (n := n) (d := d) hn
            (zero_mem _) hden_d
      · simp [g, hnd])
  have hC_to_M :
      (∑ d ∈ Finset.range C, g d) =
        ∑ d ∈ Finset.range M, g d :=
    Finset.sum_subset hCsubset (by
      intro d _hdM hdC
      have hcut : C ≤ d :=
        Nat.le_of_not_gt (mt Finset.mem_range.mpr hdC)
      by_cases hnd : n ≤ d
      · have hmem_d : P.coeff d ∈ F.Q ^ d := by
          simpa [P] using finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d
        have hden_d : den ≤ d := by
          simpa [den] using finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd
        simpa [g, C, hnd] using
          F.finiteLogNatDivEvalAtDegree_eq_zero_of_cutoff_le
            (N := N) (n := n) (d := d) hn hnd hcut hmem_d hden_d
      · simp [g, hnd])
  calc
    F.finiteLogNatDivEvalAtDegree N n n hn ((finiteLogProductCoord x y) ^ n)
        (Ideal.pow_mem_pow (F.finiteLogProductCoord_mem_Q hx hy) n)
        hden0
        = ∑ d ∈ Finset.range (P.natDegree + 1), g d := hsplit
    _ = ∑ d ∈ Finset.range C, g d := hP_to_M.trans hC_to_M.symm
    _ =
      ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        if hnd : n ≤ d then
          F.finiteLogNatDivEvalAtDegree N n d hn
            (((finiteLogProductArgPoly x y) ^ n).coeff d)
            (finiteLogProductArgPoly_pow_coeff_mem_Q_pow (F := F) hx hy n d)
            (finiteLogAdditivity_den_exponent_le (ℓ := ℓ) hn hnd)
        else 0 := by
      rfl

theorem finiteLog_eq_productHomogeneousGrid (N : ℕ)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    F.finiteLog N (finiteLogProductCoord x y) (F.finiteLogProductCoord_mem_Q hx hy) =
      finiteLogProductHomogeneousGrid (F := F) N x y hx hy := by
  classical
  rw [F.finiteLog_eq_finiteLogLocalizedPolynomial]
  unfold finiteLogLocalizedPolynomial finiteLogProductHomogeneousGrid
  refine Finset.sum_congr rfl ?_
  intro n hnC
  by_cases hn0 : n = 0
  · simp [hn0]
  · rw [dif_neg hn0, dif_neg hn0]
    rw [finiteLogProductHomogeneousGrid_term_eq (F := F) N n hn0 hx hy]

end Private

theorem finiteLog_add_add_mul (N : ℕ)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    F.finiteLog N (finiteLogProductCoord x y) (F.finiteLogProductCoord_mem_Q hx hy) =
      F.finiteLog N x hx + F.finiteLog N y hy := by
  calc
    F.finiteLog N (finiteLogProductCoord x y) (F.finiteLogProductCoord_mem_Q hx hy)
        = Private.finiteLogProductHomogeneousGrid (F := F) N x y hx hy :=
        Private.finiteLog_eq_productHomogeneousGrid (F := F) N hx hy
    _ =
      Private.finiteLogProductHomogeneousGrid (F := F) N x 0 hx (zero_mem F.Q) +
        Private.finiteLogProductHomogeneousGrid (F := F) N y 0 hy (zero_mem F.Q) :=
        Private.finiteLogProductHomogeneousGrid_add (F := F) N hx hy
    _ =
      F.finiteLog N (finiteLogProductCoord x 0)
          (F.finiteLogProductCoord_mem_Q hx (zero_mem F.Q)) +
        F.finiteLog N (finiteLogProductCoord y 0)
          (F.finiteLogProductCoord_mem_Q hy (zero_mem F.Q)) := by
        rw [← Private.finiteLog_eq_productHomogeneousGrid (F := F) N hx (zero_mem F.Q)]
        rw [← Private.finiteLog_eq_productHomogeneousGrid (F := F) N hy (zero_mem F.Q)]
    _ = F.finiteLog N x hx + F.finiteLog N y hy := by
        simp [finiteLogProductCoord]

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
